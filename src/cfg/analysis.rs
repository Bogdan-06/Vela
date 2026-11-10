//! Backward value liveness, effect-aware dead definitions and storage reuse.
use super::*;
use crate::model::MAX_FRAME_WORDS;

/// Value IDs are typed temporary locations, not necessarily SSA: a short-circuit
/// join can assign its result on both incoming edges. Every definition kills the
/// previous value for ordinary backwards liveness.
pub fn analyze(function: &Function) -> Analysis {
    let count = function.blocks.len();
    let mut live_in = vec![ValueSet::new(); count];
    let mut live_out = vec![ValueSet::new(); count];
    loop {
        let mut changed = false;
        for (id, block) in function.blocks.iter().enumerate().rev() {
            let mut outgoing = ValueSet::new();
            for successor in block.terminator.successors() {
                // Public analysis expects a verified CFG. Guarding a malformed
                // edge here still avoids an unrelated indexing panic.
                if let Some(incoming) = live_in.get(successor) {
                    outgoing.extend(incoming.iter().copied());
                }
            }
            let mut incoming = outgoing.clone();
            incoming.extend(block.terminator.used());
            for instruction in block.instructions.iter().rev() {
                if let Some(value) = instruction.defined() {
                    incoming.remove(&value);
                }
                incoming.extend(instruction.used());
            }
            if outgoing != live_out[id] || incoming != live_in[id] {
                live_out[id] = outgoing;
                live_in[id] = incoming;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut live_after = Vec::with_capacity(count);
    let mut cross_call = ValueSet::new();
    for (id, block) in function.blocks.iter().enumerate() {
        let mut live = live_out[id].clone();
        live.extend(block.terminator.used());
        let mut after = vec![ValueSet::new(); block.instructions.len()];
        for (index, instruction) in block.instructions.iter().enumerate().rev() {
            after[index] = live.clone();
            if matches!(instruction.effect(), Effect::Call | Effect::Output)
                || matches!(instruction, Instruction::StoreLocal { slot, .. }
                    if function.locals[*slot] == Type::Buffer)
            {
                for &value in &live {
                    if Some(value) != instruction.defined() {
                        cross_call.insert(value);
                    }
                }
            }
            if let Some(value) = instruction.defined() {
                live.remove(&value);
            }
            live.extend(instruction.used());
        }
        live_after.push(after);
    }
    Analysis {
        live_in,
        live_out,
        live_after,
        cross_call,
    }
}

fn edge(graph: &mut [ValueSet], a: ValueId, b: ValueId) {
    if a != b {
        graph[a].insert(b);
        graph[b].insert(a);
    }
}
fn clique(graph: &mut [ValueSet], values: &ValueSet) {
    let values: Vec<_> = values.iter().copied().collect();
    for (index, &a) in values.iter().enumerate() {
        for &b in &values[index + 1..] {
            edge(graph, a, b);
        }
    }
}

/// A small graph allocator. Only r8/r9 are available to scalar temporaries;
/// code generation reserves the other volatile registers for instructions.
/// Values surviving any call/output operation spill. Aggregate results also
/// interfere with dying operands: a field-by-field copy/constructor must not
/// overwrite an input that has not yet been consumed.
pub fn allocate(function: &Function) -> Result<Allocation, String> {
    let error = |message: String| format!("CFG function '{}': {message}", function.name);
    if function.entry >= function.blocks.len() {
        return Err(error("entry block is out of bounds".into()));
    }
    if function.values.len() > MAX_CFG_VALUES {
        return Err(error(format!(
            "value count exceeds compiler limit of {MAX_CFG_VALUES}"
        )));
    }
    for block in &function.blocks {
        if block
            .terminator
            .successors()
            .iter()
            .any(|&id| id >= function.blocks.len())
        {
            return Err(error("successor block is out of bounds".into()));
        }
        for value in block.terminator.used().into_iter().chain(
            block
                .instructions
                .iter()
                .flat_map(|i| i.used().into_iter().chain(i.defined())),
        ) {
            if value >= function.values.len() {
                return Err(error(format!("value {value} is out of bounds")));
            }
        }
    }
    for typ in function.locals.iter().chain(&function.values) {
        if typ.words() == 0 || typ.words() > MAX_FRAME_WORDS {
            return Err(error("invalid storage width".into()));
        }
    }
    let analysis = analyze(function);
    let mut graph = vec![ValueSet::new(); function.values.len()];
    for (id, block) in function.blocks.iter().enumerate() {
        clique(&mut graph, &analysis.live_in[id]);
        clique(&mut graph, &analysis.live_out[id]);
        clique(&mut graph, &block.terminator.used().into_iter().collect());
        for (index, instruction) in block.instructions.iter().enumerate() {
            let used: ValueSet = instruction.used().into_iter().collect();
            clique(&mut graph, &used);
            if let Some(value) = instruction.defined() {
                for &other in &analysis.live_after[id][index] {
                    edge(&mut graph, value, other);
                }
                if function.values[value].aggregate() {
                    for &other in &used {
                        edge(&mut graph, value, other);
                    }
                }
            }
        }
    }
    let mut locations = vec![None; function.values.len()];
    for (value, typ) in function.values.iter().enumerate() {
        if !typ.aggregate() && !analysis.cross_call.contains(&value) {
            for register in [Register::R8, Register::R9] {
                if graph[value]
                    .iter()
                    .all(|&other| locations[other] != Some(Location::Register(register)))
                {
                    locations[value] = Some(Location::Register(register));
                    break;
                }
            }
        }
    }
    let mut fixed = 0usize;
    let mut locals = Vec::with_capacity(function.locals.len());
    for typ in &function.locals {
        fixed = fixed
            .checked_add(typ.words())
            .ok_or_else(|| error("frame width overflow".into()))?;
        locals.push(
            fixed
                .checked_mul(8)
                .ok_or_else(|| error("frame byte width overflow".into()))?,
        );
    }
    let result_pointer = if function.returns.aggregate() {
        fixed = fixed
            .checked_add(1)
            .ok_or_else(|| error("result pointer width overflow".into()))?;
        Some(
            fixed
                .checked_mul(8)
                .ok_or_else(|| error("frame byte width overflow".into()))?,
        )
    } else {
        None
    };
    if fixed > MAX_FRAME_WORDS {
        return Err(error(format!(
            "native frame exceeds compiler limit of {MAX_FRAME_WORDS} words"
        )));
    }
    // Larger ranges first reduces fragmentation without claiming an optimal
    // coloring/packing. Neighbor ranges can themselves overlap when not live
    // together; first-fit treats their union as unavailable to this value.
    let mut spills: Vec<_> = (0..function.values.len())
        .filter(|&v| locations[v].is_none())
        .collect();
    spills.sort_by_key(|&value| (std::cmp::Reverse(function.values[value].words()), value));
    let mut ranges = vec![None; function.values.len()];
    let mut pool = 0usize;
    for value in spills {
        let width = function.values[value].words();
        let mut occupied: Vec<(usize, usize)> = graph[value]
            .iter()
            .filter_map(|&other| ranges[other])
            .collect();
        occupied.sort_unstable();
        let mut start = 0usize;
        for (begin, end) in occupied {
            if start
                .checked_add(width)
                .ok_or_else(|| error("temporary width overflow".into()))?
                <= begin
            {
                break;
            }
            if start < end {
                start = end;
            }
        }
        let end = start
            .checked_add(width)
            .ok_or_else(|| error("temporary width overflow".into()))?;
        pool = pool.max(end);
        let total = fixed
            .checked_add(pool)
            .ok_or_else(|| error("frame width overflow".into()))?;
        if total > MAX_FRAME_WORDS {
            return Err(error(format!(
                "native frame exceeds compiler limit of {MAX_FRAME_WORDS} words"
            )));
        }
        let offset = fixed
            .checked_add(end)
            .and_then(|n| n.checked_mul(8))
            .ok_or_else(|| error("frame byte width overflow".into()))?;
        locations[value] = Some(Location::Stack { offset });
        ranges[value] = Some((start, end));
    }
    Ok(Allocation {
        locals,
        values: locations.into_iter().map(Option::unwrap).collect(),
        result_pointer,
        words: fixed + pool,
    })
}

fn prune(function: &mut Function) {
    if function.entry >= function.blocks.len() {
        return;
    }
    let mut reachable = vec![false; function.blocks.len()];
    let mut pending = vec![function.entry];
    while let Some(id) = pending.pop() {
        if reachable[id] {
            continue;
        }
        reachable[id] = true;
        pending.extend(function.blocks[id].terminator.successors());
    }
    let mut map = vec![usize::MAX; function.blocks.len()];
    let mut next = 0;
    for (id, yes) in reachable.iter().enumerate() {
        if *yes {
            map[id] = next;
            next += 1;
        }
    }
    let mut blocks: Vec<_> = std::mem::take(&mut function.blocks)
        .into_iter()
        .enumerate()
        .filter_map(|(id, block)| reachable[id].then_some(block))
        .collect();
    for block in &mut blocks {
        match &mut block.terminator {
            Terminator::Jump(id) => *id = map[*id],
            Terminator::Branch { yes, no, .. } => {
                *yes = map[*yes];
                *no = map[*no];
            }
            _ => {}
        }
    }
    function.entry = map[function.entry];
    function.blocks = blocks;
}

/// Remove unused value IDs too, so storage planning benefits from dead code.
fn compact_values(function: &mut Function) {
    let mut active = ValueSet::new();
    for block in &function.blocks {
        active.extend(block.terminator.used());
        for instruction in &block.instructions {
            active.extend(instruction.used());
            active.extend(instruction.defined());
        }
    }
    let mut map = vec![usize::MAX; function.values.len()];
    let mut values = Vec::with_capacity(active.len());
    for value in active {
        map[value] = values.len();
        values.push(function.values[value]);
    }
    let remap_place = |place: &mut Place| {
        for projection in &mut place.projections {
            if let Projection::Index(value) = projection {
                *value = map[*value];
            }
        }
    };
    for block in &mut function.blocks {
        for instruction in &mut block.instructions {
            match instruction {
                Instruction::Define { value, rvalue } => {
                    *value = map[*value];
                    match rvalue {
                        Rvalue::Literal(_)
                        | Rvalue::LoadLocal(_)
                        | Rvalue::TakeLocal(_)
                        | Rvalue::BufferCopy(_)
                        | Rvalue::BufferLen(_) => {}
                        Rvalue::Buffer(v) | Rvalue::BufferGet { index: v, .. } => *v = map[*v],
                        Rvalue::Use(v)
                        | Rvalue::Unary(_, v)
                        | Rvalue::ArrayRepeat(v, _)
                        | Rvalue::Len(v)
                        | Rvalue::Field { base: v, .. } => *v = map[*v],
                        Rvalue::Binary(_, a, b) | Rvalue::Index { base: a, index: b } => {
                            *a = map[*a];
                            *b = map[*b];
                        }
                        Rvalue::Call(_, args) | Rvalue::Array(args) => {
                            for v in args {
                                *v = map[*v];
                            }
                        }
                        Rvalue::Record { fields, .. } => {
                            for (_, v) in fields {
                                *v = map[*v];
                            }
                        }
                        Rvalue::ReadPlace(place) => remap_place(place),
                    }
                }
                Instruction::StoreLocal { value, .. } | Instruction::Say(value) => {
                    *value = map[*value]
                }
                Instruction::StorePlace { place, value } => {
                    remap_place(place);
                    *value = map[*value];
                }
                Instruction::CheckIndex { index, .. }
                | Instruction::CheckBufferIndex { index, .. } => *index = map[*index],
                Instruction::DropLocal(_) => {}
                Instruction::BufferStore { index, value, .. } => {
                    *index = map[*index];
                    *value = map[*value];
                }
            }
        }
        match &mut block.terminator {
            Terminator::Return(value)
            | Terminator::Branch {
                condition: value, ..
            } => *value = map[*value],
            _ => {}
        }
    }
    function.values = values;
}

/// Delete only effect-free, dead definitions. Checked arithmetic/checks, unknown
/// calls, output and local writes remain observable and are never discarded.
pub fn optimize(program: &mut Program) {
    for function in &mut program.functions {
        prune(function);
        loop {
            let analysis = analyze(function);
            let mut changed = false;
            for (id, block) in function.blocks.iter_mut().enumerate() {
                block.instructions = std::mem::take(&mut block.instructions)
                    .into_iter()
                    .enumerate()
                    .filter_map(|(index, instruction)| {
                        let dead = instruction
                            .defined()
                            .is_some_and(|value| !analysis.live_after[id][index].contains(&value))
                            && matches!(instruction.effect(), Effect::Pure | Effect::ReadLocal);
                        if dead {
                            changed = true;
                            None
                        } else {
                            Some(instruction)
                        }
                    })
                    .collect();
            }
            if !changed {
                break;
            }
        }
        compact_values(function);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{ScalarType, Type};

    fn define(value: usize, rvalue: Rvalue) -> Instruction {
        Instruction::Define { value, rvalue }
    }
    fn number(value: usize, number: i64) -> Instruction {
        define(value, Rvalue::Literal(Literal::Num(number)))
    }
    fn block(instructions: Vec<Instruction>, terminator: Terminator) -> Block {
        Block {
            instructions,
            terminator,
        }
    }
    fn function(values: Vec<Type>, instructions: Vec<Instruction>, result: usize) -> Function {
        Function {
            name: "test".into(),
            params: vec![],
            returns: values[result],
            locals: vec![],
            values,
            blocks: vec![block(instructions, Terminator::Return(result))],
            entry: 0,
        }
    }
    fn range(function: &Function, allocation: &Allocation, value: usize) -> (usize, usize) {
        let Location::Stack { offset } = allocation.values[value] else {
            panic!("expected stack value {value}")
        };
        (offset / 8 - function.values[value].words(), offset / 8)
    }
    fn disjoint(a: (usize, usize), b: (usize, usize)) -> bool {
        a.1 <= b.0 || b.1 <= a.0
    }

    #[test]
    fn liveness_reaches_loop_fixed_point_and_kills_redefinitions() {
        let f = Function {
            name: "loop".into(),
            params: vec![],
            returns: Type::Num,
            locals: vec![],
            values: vec![Type::Num, Type::Flag],
            entry: 0,
            blocks: vec![
                block(
                    vec![
                        number(0, 7),
                        define(1, Rvalue::Literal(Literal::Flag(true))),
                    ],
                    Terminator::Jump(1),
                ),
                block(
                    vec![],
                    Terminator::Branch {
                        condition: 1,
                        yes: 2,
                        no: 3,
                    },
                ),
                block(
                    vec![define(1, Rvalue::Literal(Literal::Flag(false)))],
                    Terminator::Jump(1),
                ),
                block(vec![], Terminator::Return(0)),
            ],
        };
        let analysis = analyze(&f);
        assert_eq!(analysis.live_in[1], ValueSet::from([0, 1]));
        assert_eq!(analysis.live_in[2], ValueSet::from([0]));
        assert_eq!(analysis.live_after[2][0], ValueSet::from([0, 1]));
        assert!(analysis.live_in[0].is_empty());
        let allocation = allocate(&f).unwrap();
        assert_ne!(allocation.values[0], allocation.values[1]);
    }

    #[test]
    fn branch_join_result_is_not_live_before_its_incoming_definitions() {
        let f = Function {
            name: "join".into(),
            params: vec![],
            returns: Type::Num,
            locals: vec![],
            values: vec![Type::Flag, Type::Num],
            entry: 0,
            blocks: vec![
                block(
                    vec![define(0, Rvalue::Literal(Literal::Flag(true)))],
                    Terminator::Branch {
                        condition: 0,
                        yes: 1,
                        no: 2,
                    },
                ),
                block(vec![number(1, 10)], Terminator::Jump(3)),
                block(vec![number(1, 20)], Terminator::Jump(3)),
                block(vec![], Terminator::Return(1)),
            ],
        };
        let analysis = analyze(&f);
        assert!(analysis.live_in[1].is_empty());
        assert!(analysis.live_in[2].is_empty());
        assert_eq!(analysis.live_in[3], ValueSet::from([1]));
        assert!(analysis.cross_call.is_empty());
    }

    #[test]
    fn surviving_values_spill_across_calls_and_output_but_call_result_does_not() {
        let f = function(
            vec![Type::Num; 3],
            vec![
                number(0, 10),
                define(1, Rvalue::Call(1, vec![])),
                Instruction::Say(1),
                define(2, Rvalue::Binary(Binary::Add, 0, 1)),
            ],
            2,
        );
        let analysis = analyze(&f);
        assert_eq!(analysis.cross_call, ValueSet::from([0, 1]));
        let allocation = allocate(&f).unwrap();
        assert!(matches!(allocation.values[0], Location::Stack { .. }));
        assert!(matches!(allocation.values[1], Location::Stack { .. }));
        assert!(matches!(allocation.values[2], Location::Register(_)));
        let f = function(
            vec![Type::Num; 2],
            vec![number(0, 10), define(1, Rvalue::Call(1, vec![0]))],
            1,
        );
        assert!(analyze(&f).cross_call.is_empty());
        assert!(allocate(&f)
            .unwrap()
            .values
            .iter()
            .all(|location| matches!(location, Location::Register(_))));
    }

    #[test]
    fn dead_destination_writes_cannot_clobber_a_live_register() {
        let f = function(vec![Type::Num; 2], vec![number(0, 7), number(1, 99)], 0);
        let allocation = allocate(&f).unwrap();
        assert_ne!(allocation.values[0], allocation.values[1]);
    }

    #[test]
    fn disjoint_aggregate_lifetimes_reuse_one_contiguous_range() {
        let array = Type::Array(ScalarType::Num, 8);
        let f = function(
            vec![Type::Num, array, Type::Num, array, Type::Num, Type::Num],
            vec![
                number(0, 7),
                define(1, Rvalue::ArrayRepeat(0, 8)),
                define(2, Rvalue::Len(1)),
                define(3, Rvalue::ArrayRepeat(0, 8)),
                define(4, Rvalue::Len(3)),
                define(5, Rvalue::Binary(Binary::Add, 2, 4)),
            ],
            5,
        );
        let allocation = allocate(&f).unwrap();
        assert_eq!(allocation.values[1], allocation.values[3]);
        assert!(allocation.words <= 10, "{allocation:?}");
    }

    #[test]
    fn aggregate_destinations_do_not_overlap_dying_call_or_copy_sources() {
        let array = Type::Array(ScalarType::Num, 8);
        for producer in [Rvalue::Call(1, vec![1]), Rvalue::Use(1)] {
            let f = function(
                vec![Type::Num, array, array],
                vec![
                    number(0, 7),
                    define(1, Rvalue::ArrayRepeat(0, 8)),
                    define(2, producer),
                ],
                2,
            );
            let allocation = allocate(&f).unwrap();
            assert!(
                disjoint(range(&f, &allocation, 1), range(&f, &allocation, 2)),
                "{allocation:?}"
            );
            assert_eq!(allocation.result_pointer, Some(8));
        }
    }

    #[test]
    fn aggregate_constructor_cannot_overwrite_dying_spilled_scalar_inputs() {
        let array = Type::Array(ScalarType::Num, 8);
        let f = function(
            vec![Type::Num, array],
            vec![
                number(0, 7),
                Instruction::Say(0),
                define(1, Rvalue::ArrayRepeat(0, 8)),
            ],
            1,
        );
        let allocation = allocate(&f).unwrap();
        assert!(
            disjoint(range(&f, &allocation, 0), range(&f, &allocation, 1)),
            "{allocation:?}"
        );
    }

    #[test]
    fn simultaneous_aggregate_call_arguments_have_distinct_storage() {
        let array = Type::Array(ScalarType::Num, 8);
        let f = function(
            vec![Type::Num, array, array, Type::Num],
            vec![
                number(0, 7),
                define(1, Rvalue::ArrayRepeat(0, 8)),
                define(2, Rvalue::ArrayRepeat(0, 8)),
                define(3, Rvalue::Call(1, vec![1, 2])),
            ],
            3,
        );
        let allocation = allocate(&f).unwrap();
        assert!(disjoint(
            range(&f, &allocation, 1),
            range(&f, &allocation, 2)
        ));
    }

    #[test]
    fn reused_ranges_fit_even_when_sum_of_temporary_sizes_exceeds_frame_cap() {
        let array = Type::Array(ScalarType::Num, 4096);
        let mut values = vec![Type::Num];
        let mut instructions = vec![number(0, 7)];
        for _ in 0..20 {
            let aggregate = values.len();
            values.push(array);
            let length = values.len();
            values.push(Type::Num);
            instructions.extend([
                define(aggregate, Rvalue::ArrayRepeat(0, 4096)),
                define(length, Rvalue::Len(aggregate)),
                Instruction::Say(length),
            ]);
        }
        let f = function(values, instructions, 0);
        assert!(f.values.iter().map(|typ| typ.words()).sum::<usize>() > MAX_FRAME_WORDS);
        assert!(allocate(&f).unwrap().words <= 4098);
    }

    #[test]
    fn storage_errors_are_diagnostic_and_size_arithmetic_is_checked() {
        let mut f = function(
            vec![Type::Num, Type::Array(ScalarType::Num, 4096)],
            vec![number(0, 7), define(1, Rvalue::ArrayRepeat(0, 4096))],
            0,
        );
        f.locals = vec![Type::Array(ScalarType::Num, 4096); 16];
        assert!(allocate(&f).unwrap_err().contains("native frame exceeds"));
        f.locals = vec![Type::Record {
            id: 0,
            words: usize::MAX,
        }];
        assert!(allocate(&f).unwrap_err().contains("invalid storage width"));
        f.entry = 100;
        assert!(allocate(&f).unwrap_err().contains("entry block"));
    }

    #[test]
    fn dce_removes_pure_chains_but_preserves_faults_calls_output_checks_and_writes() {
        let mut f = function(
            vec![
                Type::Num,
                Type::Num,
                Type::Num,
                Type::Num,
                Type::Flag,
                Type::Array(ScalarType::Num, 8),
                Type::Num,
            ],
            vec![
                number(0, 1),
                number(1, 0),
                define(2, Rvalue::Binary(Binary::Div, 0, 1)),
                define(3, Rvalue::Call(1, vec![])),
                define(4, Rvalue::Literal(Literal::Flag(false))),
                define(5, Rvalue::ArrayRepeat(0, 8)),
                Instruction::CheckIndex {
                    index: 0,
                    length: 8,
                },
                Instruction::Say(0),
                Instruction::StoreLocal { slot: 0, value: 0 },
                define(6, Rvalue::LoadLocal(0)),
            ],
            0,
        );
        f.locals = vec![Type::Num];
        let mut p = Program {
            functions: vec![f],
            records: vec![],
            main: 0,
        };
        optimize(&mut p);
        let f = &p.functions[0];
        let instructions = &f.blocks[0].instructions;
        assert_eq!(f.values.len(), 4);
        assert!(instructions.iter().any(|i| matches!(
            i,
            Instruction::Define {
                rvalue: Rvalue::Binary(Binary::Div, _, _),
                ..
            }
        )));
        assert!(instructions.iter().any(|i| matches!(
            i,
            Instruction::Define {
                rvalue: Rvalue::Call(..),
                ..
            }
        )));
        for effect in [
            Effect::Checked,
            Effect::Call,
            Effect::Output,
            Effect::WriteLocal,
        ] {
            assert!(instructions.iter().any(|i| i.effect() == effect));
        }
        assert!(!instructions.iter().any(|i| matches!(
            i,
            Instruction::Define {
                rvalue: Rvalue::ArrayRepeat(..) | Rvalue::LoadLocal(_),
                ..
            }
        )));
    }

    #[test]
    fn dce_iterates_dependencies_and_prunes_only_unreachable_effects() {
        let mut f = function(
            vec![Type::Num, Type::Num, Type::Flag, Type::Num],
            vec![
                number(0, 7),
                number(1, 9),
                define(2, Rvalue::Binary(Binary::Eq, 1, 1)),
            ],
            0,
        );
        f.blocks.push(block(
            vec![number(3, 99), Instruction::Say(3)],
            Terminator::Return(3),
        ));
        let mut p = Program {
            functions: vec![f],
            records: vec![],
            main: 0,
        };
        optimize(&mut p);
        assert_eq!(p.functions[0].blocks.len(), 1);
        assert_eq!(p.functions[0].values.len(), 1);
        assert_eq!(p.functions[0].blocks[0].instructions.len(), 1);
        assert!(matches!(
            p.functions[0].blocks[0].terminator,
            Terminator::Return(0)
        ));
    }
}
