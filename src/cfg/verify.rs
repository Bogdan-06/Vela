//! Type, edge and path-sensitive availability checks for executable CFGs.
use super::*;
use crate::model::MAX_ARRAY_LEN;

#[derive(Clone, Debug, PartialEq, Eq)]
struct State {
    locals: ValueSet,
    values: ValueSet,
    checks: BTreeSet<(ValueId, usize)>,
    buffer_checks: BTreeSet<(usize, ValueId)>,
    /// May-own sets are intentionally never filtered by ordinary liveness:
    /// an unused owner still has to be transferred or destroyed.
    owned_values: ValueSet,
    owned_locals: ValueSet,
}
impl State {
    fn intersection(&mut self, other: &Self) {
        self.locals.retain(|id| other.locals.contains(id));
        self.values.retain(|id| other.values.contains(id));
        self.checks.retain(|check| other.checks.contains(check));
        self.buffer_checks
            .retain(|check| other.buffer_checks.contains(check));
        self.owned_values.extend(other.owned_values.iter().copied());
        self.owned_locals.extend(other.owned_locals.iter().copied());
    }
    fn consume(&mut self, value: ValueId, function: &Function) {
        if function.values[value] == Type::Buffer {
            self.values.remove(&value);
            self.owned_values.remove(&value);
        }
    }
    fn invalidate_local(&mut self, slot: usize) {
        self.locals.remove(&slot);
        self.owned_locals.remove(&slot);
        self.buffer_checks.retain(|(owner, _)| *owner != slot);
    }
    fn transfer(&mut self, instruction: &Instruction, function: &Function) {
        match instruction {
            Instruction::Define { value, rvalue } => {
                match rvalue {
                    Rvalue::Call(_, arguments) => {
                        for argument in arguments {
                            self.consume(*argument, function);
                        }
                    }
                    Rvalue::TakeLocal(slot) => self.invalidate_local(*slot),
                    _ => {}
                }
                self.checks.retain(|(index, _)| index != value);
                self.buffer_checks.retain(|(_, index)| index != value);
                self.values.insert(*value);
                if function.values[*value] == Type::Buffer {
                    self.owned_values.insert(*value);
                }
            }
            Instruction::StoreLocal { slot, value } => {
                self.consume(*value, function);
                self.buffer_checks.retain(|(owner, _)| owner != slot);
                self.locals.insert(*slot);
                if function.locals[*slot] == Type::Buffer {
                    self.owned_locals.insert(*slot);
                }
            }
            Instruction::CheckIndex { index, length } => {
                self.checks.insert((*index, *length));
            }
            Instruction::CheckBufferIndex { slot, index } => {
                self.buffer_checks.insert((*slot, *index));
            }
            Instruction::DropLocal(slot) => self.invalidate_local(*slot),
            _ => {}
        }
    }
}

/// Validate every block's shape/types, and every reachable path's initialized
/// locals, defined temporary values and dominating matching bounds checks.
pub fn verify(program: &Program) -> Result<(), String> {
    crate::ir::verify_records(&program.records).map_err(|e| format!("CFG records: {e}"))?;
    let main = program
        .functions
        .get(program.main)
        .ok_or("CFG entry function index is out of bounds")?;
    if !main.params.is_empty() || main.returns != Type::Num {
        return Err("CFG entry must have no parameters and return num".into());
    }
    for function in &program.functions {
        Checker { program, function }.function()?;
    }
    Ok(())
}
struct Checker<'a> {
    program: &'a Program,
    function: &'a Function,
}
impl Checker<'_> {
    fn error(&self, message: impl std::fmt::Display) -> String {
        format!("CFG function '{}': {message}", self.function.name)
    }
    fn require(&self, actual: Type, wanted: Type, context: &str) -> Result<(), String> {
        if actual != wanted {
            return Err(self.error(format!("{context} expects {wanted}, got {actual}")));
        }
        Ok(())
    }
    fn value(&self, id: ValueId, state: Option<&State>) -> Result<Type, String> {
        let typ = self
            .function
            .values
            .get(id)
            .copied()
            .ok_or_else(|| self.error(format!("value {id} is out of bounds")))?;
        if state.is_some_and(|state| !state.values.contains(&id)) {
            return Err(self.error(format!("value {id} is not definitely defined")));
        }
        Ok(typ)
    }
    fn local(&self, slot: usize, state: Option<&State>) -> Result<Type, String> {
        let typ = self
            .function
            .locals
            .get(slot)
            .copied()
            .ok_or_else(|| self.error(format!("local {slot} is out of bounds")))?;
        if state.is_some_and(|state| !state.locals.contains(&slot)) {
            return Err(self.error(format!("local {slot} is not definitely initialized")));
        }
        Ok(typ)
    }
    fn checked(&self, index: ValueId, length: usize, state: Option<&State>) -> Result<(), String> {
        if state.is_some_and(|state| !state.checks.contains(&(index, length))) {
            return Err(self.error(format!(
                "index value {index} lacks a dominating bounds check for length {length}"
            )));
        }
        Ok(())
    }
    fn buffer(&self, slot: usize, state: Option<&State>) -> Result<(), String> {
        self.require(self.local(slot, state)?, Type::Buffer, "buffer local")
    }
    fn buffer_checked(
        &self,
        slot: usize,
        index: ValueId,
        state: Option<&State>,
    ) -> Result<(), String> {
        self.buffer(slot, state)?;
        self.require(self.value(index, state)?, Type::Num, "buffer index")?;
        if state.is_some_and(|s| !s.buffer_checks.contains(&(slot, index))) {
            return Err(self.error(format!(
                "buffer local {slot} index {index} lacks a dominating bounds check"
            )));
        }
        Ok(())
    }
    fn place(&self, place: &Place, state: Option<&State>) -> Result<Type, String> {
        let mut typ = self.local(place.slot, state)?;
        for projection in &place.projections {
            match projection {
                Projection::Field(field) => {
                    let Type::Record { id, .. } = typ else {
                        return Err(self.error("field projection requires a record"));
                    };
                    typ = self.program.records[id]
                        .fields
                        .get(*field)
                        .ok_or_else(|| self.error(format!("field {field} is out of bounds")))?
                        .typ;
                }
                Projection::Index(index) => {
                    let actual = self.value(*index, state)?;
                    self.require(actual, Type::Num, "array index")?;
                    let Type::Array(element, length) = typ else {
                        return Err(self.error("index projection requires an array"));
                    };
                    self.checked(*index, length, state)?;
                    typ = element.typ();
                }
            }
        }
        Ok(typ)
    }
    fn rvalue(&self, value: &Rvalue, state: Option<&State>) -> Result<Type, String> {
        match value {
            Rvalue::Literal(value) => match value {
                Literal::Num(_) => Ok(Type::Num),
                Literal::Flag(_) => Ok(Type::Flag),
                Literal::Text(text) => {
                    if text.contains('\0') {
                        Err(self.error("text literal contains embedded NUL"))
                    } else {
                        Ok(Type::Text)
                    }
                }
            },
            Rvalue::Use(value) => {
                let typ = self.value(*value, state)?;
                if typ == Type::Buffer {
                    return Err(self.error("buffer temporaries cannot be copied with Use"));
                }
                Ok(typ)
            }
            Rvalue::LoadLocal(slot) => {
                let typ = self.local(*slot, state)?;
                if typ == Type::Buffer {
                    return Err(self.error("buffer local must be moved with TakeLocal"));
                }
                Ok(typ)
            }
            Rvalue::ReadPlace(place) => {
                let typ = self.place(place, state)?;
                if typ == Type::Buffer {
                    return Err(self.error("buffer owner cannot be copied through ReadPlace"));
                }
                Ok(typ)
            }
            Rvalue::TakeLocal(slot) | Rvalue::BufferCopy(slot) => {
                self.buffer(*slot, state)?;
                Ok(Type::Buffer)
            }
            Rvalue::Buffer(length) => {
                self.require(self.value(*length, state)?, Type::Num, "buffer length")?;
                Ok(Type::Buffer)
            }
            Rvalue::BufferLen(slot) => {
                self.buffer(*slot, state)?;
                Ok(Type::Num)
            }
            Rvalue::BufferGet { slot, index } => {
                self.buffer_checked(*slot, *index, state)?;
                Ok(Type::Num)
            }
            Rvalue::Unary(operator, value) => {
                let actual = self.value(*value, state)?;
                let wanted = match operator {
                    Unary::Neg => Type::Num,
                    Unary::Not => Type::Flag,
                };
                self.require(actual, wanted, "unary operand")?;
                Ok(wanted)
            }
            Rvalue::Binary(operator, left, right) => {
                let left = self.value(*left, state)?;
                let right = self.value(*right, state)?;
                match operator {
                    Binary::And | Binary::Or => {
                        self.require(left, Type::Flag, "boolean left operand")?;
                        self.require(right, Type::Flag, "boolean right operand")?;
                        Ok(Type::Flag)
                    }
                    Binary::Eq | Binary::Ne => {
                        if left == right && matches!(left, Type::Num | Type::Flag) {
                            Ok(Type::Flag)
                        } else {
                            Err(self.error("equality requires matching num or flag operands"))
                        }
                    }
                    Binary::Add | Binary::Sub | Binary::Mul | Binary::Div | Binary::Rem => {
                        self.require(left, Type::Num, "arithmetic left operand")?;
                        self.require(right, Type::Num, "arithmetic right operand")?;
                        Ok(Type::Num)
                    }
                    Binary::Lt | Binary::Le | Binary::Gt | Binary::Ge => {
                        self.require(left, Type::Num, "comparison left operand")?;
                        self.require(right, Type::Num, "comparison right operand")?;
                        Ok(Type::Flag)
                    }
                }
            }
            Rvalue::Call(function, arguments) => {
                let callee = self
                    .program
                    .functions
                    .get(*function)
                    .ok_or_else(|| self.error(format!("callee {function} is out of bounds")))?;
                if arguments.len() != callee.params.len() {
                    return Err(
                        self.error(format!("call '{}' has wrong argument count", callee.name))
                    );
                }
                let mut consumed = ValueSet::new();
                for (value, wanted) in arguments.iter().zip(&callee.params) {
                    let actual = self.value(*value, state)?;
                    self.require(actual, *wanted, "call argument")?;
                    if actual == Type::Buffer && !consumed.insert(*value) {
                        return Err(
                            self.error(format!("buffer value {value} consumed twice by call"))
                        );
                    }
                }
                Ok(callee.returns)
            }
            Rvalue::Array(values) => {
                if !(1..=MAX_ARRAY_LEN).contains(&values.len()) {
                    return Err(self.error("array literal length is out of range"));
                }
                let typ = self.value(values[0], state)?;
                let element = typ
                    .scalar()
                    .ok_or_else(|| self.error("array elements must be scalar"))?;
                for value in &values[1..] {
                    let actual = self.value(*value, state)?;
                    self.require(actual, typ, "array element")?;
                }
                Ok(Type::Array(element, values.len()))
            }
            Rvalue::ArrayRepeat(value, length) => {
                if !(1..=MAX_ARRAY_LEN).contains(length) {
                    return Err(self.error("array repeat length is out of range"));
                }
                let element = self
                    .value(*value, state)?
                    .scalar()
                    .ok_or_else(|| self.error("array repeat requires a scalar"))?;
                Ok(Type::Array(element, *length))
            }
            Rvalue::Index { base, index } => {
                let base = self.value(*base, state)?;
                let index_type = self.value(*index, state)?;
                self.require(index_type, Type::Num, "array index")?;
                let Type::Array(element, length) = base else {
                    return Err(self.error("index read requires an array"));
                };
                self.checked(*index, length, state)?;
                Ok(element.typ())
            }
            Rvalue::Len(value) => {
                if !matches!(self.value(*value, state)?, Type::Array(..)) {
                    return Err(self.error("len requires an array"));
                }
                Ok(Type::Num)
            }
            Rvalue::Record { record, fields } => {
                let declaration = self
                    .program
                    .records
                    .get(*record)
                    .ok_or_else(|| self.error(format!("record {record} is out of bounds")))?;
                let mut seen = vec![false; declaration.fields.len()];
                for (index, value) in fields {
                    let field = declaration
                        .fields
                        .get(*index)
                        .ok_or_else(|| self.error(format!("field {index} is out of bounds")))?;
                    if seen[*index] {
                        return Err(self.error("duplicate record initializer"));
                    }
                    seen[*index] = true;
                    let actual = self.value(*value, state)?;
                    self.require(actual, field.typ, "record field initializer")?;
                }
                if seen.iter().any(|seen| !seen) {
                    return Err(self.error("missing record initializer"));
                }
                Ok(Type::Record {
                    id: *record,
                    words: declaration.words,
                })
            }
            Rvalue::Field { base, field } => {
                let Type::Record { id, .. } = self.value(*base, state)? else {
                    return Err(self.error("field read requires a record"));
                };
                self.program.records[id]
                    .fields
                    .get(*field)
                    .map(|f| f.typ)
                    .ok_or_else(|| self.error(format!("field {field} is out of bounds")))
            }
        }
    }
    fn instruction(&self, instruction: &Instruction, state: Option<&State>) -> Result<(), String> {
        match instruction {
            Instruction::Define { value, rvalue } => {
                let wanted = self.value(*value, None)?;
                let actual = self.rvalue(rvalue, state)?;
                self.require(actual, wanted, "defined value")?;
                if state.is_some_and(|s| s.owned_values.contains(value)) {
                    return Err(
                        self.error(format!("redefinition would leak live buffer value {value}"))
                    );
                }
            }
            Instruction::StoreLocal { slot, value } => {
                let wanted = self.local(*slot, None)?;
                let actual = self.value(*value, state)?;
                self.require(actual, wanted, "local store")?;
            }
            Instruction::StorePlace { place, value } => {
                if place.projections.is_empty() {
                    return Err(self.error("projected store requires at least one projection"));
                }
                let wanted = self.place(place, state)?;
                let actual = self.value(*value, state)?;
                self.require(actual, wanted, "projected store")?;
            }
            Instruction::Say(value) => {
                if self.value(*value, state)?.scalar().is_none() {
                    return Err(self.error("say requires a scalar"));
                }
            }
            Instruction::CheckIndex { index, length } => {
                if !(1..=MAX_ARRAY_LEN).contains(length) {
                    return Err(self.error("bounds check length is out of range"));
                }
                let actual = self.value(*index, state)?;
                self.require(actual, Type::Num, "bounds check index")?;
            }
            Instruction::DropLocal(slot) => {
                self.buffer(*slot, None)?;
            }
            Instruction::CheckBufferIndex { slot, index } => {
                self.buffer(*slot, state)?;
                self.require(
                    self.value(*index, state)?,
                    Type::Num,
                    "buffer bounds check index",
                )?;
            }
            Instruction::BufferStore { slot, index, value } => {
                self.buffer_checked(*slot, *index, state)?;
                self.require(
                    self.value(*value, state)?,
                    Type::Num,
                    "buffer stored element",
                )?;
            }
        }
        Ok(())
    }
    fn terminator(&self, terminator: &Terminator, state: Option<&State>) -> Result<(), String> {
        match terminator {
            Terminator::Return(value) => {
                let actual = self.value(*value, state)?;
                self.require(actual, self.function.returns, "return value")?;
                if let Some(state) = state {
                    if !state.owned_locals.is_empty() {
                        return Err(self.error("return leaks live buffer local; insert cleanup"));
                    }
                    if state.owned_values.iter().any(|v| *v != *value) {
                        return Err(self.error("return leaks unconsumed buffer temporary"));
                    }
                }
            }
            Terminator::Branch { condition, .. } => {
                let actual = self.value(*condition, state)?;
                self.require(actual, Type::Flag, "branch condition")?;
            }
            _ => {}
        }
        Ok(())
    }
    fn function(&self) -> Result<(), String> {
        let function = self.function;
        let blocks = function.blocks.len();
        if blocks == 0 || blocks > MAX_CFG_BLOCKS {
            return Err(self.error("block count is outside compiler limits"));
        }
        if function.values.len() > MAX_CFG_VALUES {
            return Err(self.error("value count exceeds compiler limit"));
        }
        if function.entry >= blocks {
            return Err(self.error("entry block is out of bounds"));
        }
        if function.params.len() > 6 {
            return Err(self.error("function exceeds six source parameters"));
        }
        if !function.locals.starts_with(&function.params) {
            return Err(self.error("parameter types must match local prefix"));
        }
        for typ in function
            .locals
            .iter()
            .chain(&function.params)
            .chain(&function.values)
            .chain(std::iter::once(&function.returns))
        {
            crate::ir::canonical_type(*typ, &self.program.records).map_err(|e| self.error(e))?;
        }
        let mut predecessors = vec![vec![]; blocks];
        // All blocks get structural and type validation, including unreachable ones.
        for (id, block) in function.blocks.iter().enumerate() {
            for successor in block.terminator.successors() {
                if successor >= blocks {
                    return Err(
                        self.error(format!("block {id} successor {successor} is out of bounds"))
                    );
                }
                predecessors[successor].push(id);
            }
            for instruction in &block.instructions {
                self.instruction(instruction, None)?;
            }
            self.terminator(&block.terminator, None)?;
        }
        if !predecessors[function.entry].is_empty() {
            return Err(self.error("entry block must not have predecessors"));
        }
        let mut reachable = vec![false; blocks];
        let mut pending = vec![function.entry];
        while let Some(id) = pending.pop() {
            if reachable[id] {
                continue;
            }
            reachable[id] = true;
            pending.extend(function.blocks[id].terminator.successors());
        }
        for (id, block) in function.blocks.iter().enumerate() {
            if reachable[id] && matches!(block.terminator, Terminator::Unreachable) {
                return Err(self.error(format!(
                    "reachable block {id} has an unreachable terminator"
                )));
            }
        }
        let initial = State {
            locals: (0..function.params.len()).collect(),
            values: ValueSet::new(),
            checks: BTreeSet::new(),
            buffer_checks: BTreeSet::new(),
            owned_values: ValueSet::new(),
            owned_locals: function
                .params
                .iter()
                .enumerate()
                .filter_map(|(slot, typ)| (*typ == Type::Buffer).then_some(slot))
                .collect(),
        };
        // Structural validation above makes the liveness analysis safe. Values
        // and locals never read again need not occupy availability sets on each
        // later block. Checks are likewise useful only while their index lives.
        let value_live_out = super::analyze(function).live_out;
        let local_live_out = local_liveness(function, &predecessors);
        // None represents TOP, not a materialized universe per block. The first
        // known path establishes an upper bound; later paths can only reduce it.
        let mut incoming: Vec<Option<State>> = vec![None; blocks];
        let mut outgoing: Vec<Option<State>> = vec![None; blocks];
        let mut pending = std::collections::VecDeque::from([function.entry]);
        let mut queued = vec![false; blocks];
        queued[function.entry] = true;
        while let Some(id) = pending.pop_front() {
            queued[id] = false;
            let mut state = if id == function.entry {
                Some(initial.clone())
            } else {
                None
            };
            if id != function.entry {
                for &predecessor in &predecessors[id] {
                    if !reachable[predecessor] {
                        continue;
                    }
                    if let Some(previous) = &outgoing[predecessor] {
                        if let Some(state) = &mut state {
                            state.intersection(previous);
                        } else {
                            state = Some(previous.clone());
                        }
                    }
                }
            }
            let Some(mut state) = state else { continue };
            incoming[id] = Some(state.clone());
            for instruction in &function.blocks[id].instructions {
                state.transfer(instruction, function);
            }
            state
                .values
                .retain(|value| value_live_out[id].contains(value));
            state
                .checks
                .retain(|(value, _)| value_live_out[id].contains(value));
            state
                .buffer_checks
                .retain(|(_, value)| value_live_out[id].contains(value));
            state
                .locals
                .retain(|slot| local_live_out[id].contains(slot));
            if outgoing[id].as_ref() != Some(&state) {
                outgoing[id] = Some(state);
                for successor in function.blocks[id].terminator.successors() {
                    if !queued[successor] {
                        pending.push_back(successor);
                        queued[successor] = true;
                    }
                }
            }
        }
        for (id, block) in function.blocks.iter().enumerate() {
            if !reachable[id] {
                continue;
            }
            let mut state = incoming[id]
                .clone()
                .expect("reachable block receives an entry path");
            for instruction in &block.instructions {
                self.instruction(instruction, Some(&state))
                    .map_err(|e| format!("{e} in block {id}"))?;
                state.transfer(instruction, function);
            }
            self.terminator(&block.terminator, Some(&state))?;
        }
        Ok(())
    }
}

/// Backward local liveness prevents a long series of unrelated local stores
/// from being retained in every later block's definite-initialization state.
fn local_liveness(function: &Function, predecessors: &[Vec<BlockId>]) -> Vec<ValueSet> {
    let count = function.blocks.len();
    let mut uses = vec![ValueSet::new(); count];
    let mut defs = vec![ValueSet::new(); count];
    for (id, block) in function.blocks.iter().enumerate() {
        for instruction in &block.instructions {
            let read = match instruction {
                Instruction::Define {
                    rvalue:
                        Rvalue::LoadLocal(slot)
                        | Rvalue::TakeLocal(slot)
                        | Rvalue::BufferCopy(slot)
                        | Rvalue::BufferLen(slot)
                        | Rvalue::BufferGet { slot, .. },
                    ..
                }
                | Instruction::CheckBufferIndex { slot, .. }
                | Instruction::BufferStore { slot, .. } => Some(*slot),
                Instruction::Define {
                    rvalue: Rvalue::ReadPlace(place),
                    ..
                }
                | Instruction::StorePlace { place, .. } => Some(place.slot),
                _ => None,
            };
            if let Some(slot) = read {
                if !defs[id].contains(&slot) {
                    uses[id].insert(slot);
                }
            }
            match instruction {
                Instruction::StoreLocal { slot, .. }
                | Instruction::DropLocal(slot)
                | Instruction::Define {
                    rvalue: Rvalue::TakeLocal(slot),
                    ..
                } => {
                    defs[id].insert(*slot);
                }
                _ => {}
            }
        }
    }
    let mut live_in = vec![ValueSet::new(); count];
    let mut live_out = vec![ValueSet::new(); count];
    let mut pending: std::collections::VecDeque<_> = (0..count).rev().collect();
    let mut queued = vec![true; count];
    while let Some(id) = pending.pop_front() {
        queued[id] = false;
        let mut out = ValueSet::new();
        for successor in function.blocks[id].terminator.successors() {
            out.extend(live_in[successor].iter().copied());
        }
        let mut input = uses[id].clone();
        input.extend(out.difference(&defs[id]).copied());
        live_out[id] = out;
        if live_in[id] != input {
            live_in[id] = input;
            for &pred in &predecessors[id] {
                if !queued[pred] {
                    pending.push_back(pred);
                    queued[pred] = true;
                }
            }
        }
    }
    live_out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::ScalarType;
    fn define(value: usize, number: i64) -> Instruction {
        Instruction::Define {
            value,
            rvalue: Rvalue::Literal(Literal::Num(number)),
        }
    }
    fn block(instructions: Vec<Instruction>, terminator: Terminator) -> Block {
        Block {
            instructions,
            terminator,
        }
    }
    fn program(locals: Vec<Type>, values: Vec<Type>, blocks: Vec<Block>) -> Program {
        Program {
            records: vec![],
            main: 0,
            functions: vec![Function {
                name: "main".into(),
                params: vec![],
                returns: Type::Num,
                locals,
                values,
                blocks,
                entry: 0,
            }],
        }
    }
    fn rejects(program: &Program, message: &str) {
        let error = verify(program).expect_err("malformed CFG accepted");
        assert!(error.contains(message), "expected {message}, got {error}");
    }
    #[test]
    fn validates_edges_entry_types_and_all_unreachable_structures() {
        let mut p = program(
            vec![],
            vec![Type::Num],
            vec![block(vec![define(0, 0)], Terminator::Return(0))],
        );
        verify(&p).unwrap();
        p.functions[0].blocks[0].terminator = Terminator::Jump(3);
        rejects(&p, "successor 3");
        p.functions[0].blocks[0].terminator = Terminator::Jump(0);
        rejects(&p, "entry block must not");
        p.functions[0].blocks[0].terminator = Terminator::Unreachable;
        rejects(&p, "reachable block 0");
        p.functions[0].blocks[0].terminator = Terminator::Return(0);
        p.functions[0]
            .blocks
            .push(block(vec![Instruction::Say(7)], Terminator::Unreachable));
        rejects(&p, "value 7");
    }
    #[test]
    fn branch_merges_require_definition_on_every_falling_path() {
        let mut p = program(
            vec![],
            vec![Type::Flag, Type::Num],
            vec![
                block(
                    vec![Instruction::Define {
                        value: 0,
                        rvalue: Rvalue::Literal(Literal::Flag(true)),
                    }],
                    Terminator::Branch {
                        condition: 0,
                        yes: 1,
                        no: 2,
                    },
                ),
                block(vec![define(1, 7)], Terminator::Jump(3)),
                block(vec![], Terminator::Jump(3)),
                block(vec![], Terminator::Return(1)),
            ],
        );
        rejects(&p, "not definitely defined");
        p.functions[0].blocks[2].instructions.push(define(1, 8));
        verify(&p).unwrap();
    }
    #[test]
    fn returning_branch_does_not_poison_other_branch_initialization() {
        let p = program(
            vec![Type::Num],
            vec![Type::Flag, Type::Num, Type::Num],
            vec![
                block(
                    vec![
                        Instruction::Define {
                            value: 0,
                            rvalue: Rvalue::Literal(Literal::Flag(false)),
                        },
                        define(1, 0),
                    ],
                    Terminator::Branch {
                        condition: 0,
                        yes: 1,
                        no: 2,
                    },
                ),
                block(vec![], Terminator::Return(1)),
                block(
                    vec![Instruction::StoreLocal { slot: 0, value: 1 }],
                    Terminator::Jump(3),
                ),
                block(
                    vec![Instruction::Define {
                        value: 2,
                        rvalue: Rvalue::LoadLocal(0),
                    }],
                    Terminator::Return(2),
                ),
            ],
        );
        verify(&p).unwrap();
    }
    #[test]
    fn loop_body_only_definitions_are_not_available_after_zero_iterations() {
        let p = program(
            vec![Type::Num],
            vec![Type::Flag, Type::Num, Type::Num],
            vec![
                block(
                    vec![Instruction::Define {
                        value: 0,
                        rvalue: Rvalue::Literal(Literal::Flag(false)),
                    }],
                    Terminator::Jump(1),
                ),
                block(
                    vec![],
                    Terminator::Branch {
                        condition: 0,
                        yes: 2,
                        no: 3,
                    },
                ),
                block(
                    vec![define(1, 5), Instruction::StoreLocal { slot: 0, value: 1 }],
                    Terminator::Jump(1),
                ),
                block(
                    vec![Instruction::Define {
                        value: 2,
                        rvalue: Rvalue::LoadLocal(0),
                    }],
                    Terminator::Return(2),
                ),
            ],
        );
        rejects(&p, "not definitely initialized");
    }
    fn indexing() -> Program {
        program(
            vec![Type::Array(ScalarType::Num, 2)],
            vec![Type::Num, Type::Array(ScalarType::Num, 2), Type::Num],
            vec![block(
                vec![
                    define(0, 0),
                    Instruction::Define {
                        value: 1,
                        rvalue: Rvalue::ArrayRepeat(0, 2),
                    },
                    Instruction::StoreLocal { slot: 0, value: 1 },
                    Instruction::CheckIndex {
                        index: 0,
                        length: 2,
                    },
                    Instruction::Define {
                        value: 2,
                        rvalue: Rvalue::ReadPlace(Place {
                            slot: 0,
                            projections: vec![Projection::Index(0)],
                        }),
                    },
                ],
                Terminator::Return(2),
            )],
        )
    }
    #[test]
    fn bounds_checks_must_match_shape_and_survive_index_redefinitions() {
        let mut p = indexing();
        verify(&p).unwrap();
        p.functions[0].blocks[0].instructions[3] = Instruction::CheckIndex {
            index: 0,
            length: 3,
        };
        rejects(&p, "length 2");
        p = indexing();
        p.functions[0].blocks[0]
            .instructions
            .insert(4, define(0, 1));
        rejects(&p, "dominating bounds check");
        p.functions[0].blocks[0].instructions.insert(
            5,
            Instruction::CheckIndex {
                index: 0,
                length: 2,
            },
        );
        verify(&p).unwrap();
    }
    #[test]
    fn projected_store_checks_before_rhs_value_is_used() {
        let mut p = indexing();
        p.functions[0].blocks[0].instructions.pop();
        p.functions[0].blocks[0]
            .instructions
            .push(Instruction::StorePlace {
                place: Place {
                    slot: 0,
                    projections: vec![Projection::Index(0)],
                },
                value: 0,
            });
        p.functions[0].blocks[0].terminator = Terminator::Return(0);
        verify(&p).unwrap();
        p.functions[0].blocks[0].instructions.remove(3);
        rejects(&p, "dominating bounds check");
    }
    #[test]
    fn malformed_types_calls_fields_and_constructors_are_rejected() {
        let mut p = program(
            vec![],
            vec![Type::Flag],
            vec![block(vec![define(0, 0)], Terminator::Return(0))],
        );
        rejects(&p, "defined value expects flag");
        p.functions[0].values[0] = Type::Num;
        p.functions[0].blocks[0].instructions[0] = Instruction::Define {
            value: 0,
            rvalue: Rvalue::Call(9, vec![]),
        };
        rejects(&p, "callee 9");
        p.functions[0].blocks[0].instructions[0] = Instruction::Define {
            value: 0,
            rvalue: Rvalue::Field { base: 0, field: 0 },
        };
        rejects(&p, "field read requires");
        p.functions[0].blocks[0].instructions[0] = Instruction::Define {
            value: 0,
            rvalue: Rvalue::Record {
                record: 3,
                fields: vec![],
            },
        };
        rejects(&p, "record 3");
    }
    #[test]
    fn check_available_on_only_one_branch_does_not_dominate_merge() {
        let mut p = indexing();
        let initial = p.functions[0].blocks[0].instructions[..3].to_vec();
        p.functions[0].values.push(Type::Flag);
        let mut initial = initial;
        initial.push(Instruction::Define {
            value: 3,
            rvalue: Rvalue::Literal(Literal::Flag(true)),
        });
        p.functions[0].blocks = vec![
            block(
                initial,
                Terminator::Branch {
                    condition: 3,
                    yes: 1,
                    no: 2,
                },
            ),
            block(
                vec![Instruction::CheckIndex {
                    index: 0,
                    length: 2,
                }],
                Terminator::Jump(3),
            ),
            block(vec![], Terminator::Jump(3)),
            block(
                vec![Instruction::Define {
                    value: 2,
                    rvalue: Rvalue::Index { base: 1, index: 0 },
                }],
                Terminator::Return(2),
            ),
        ];
        rejects(&p, "dominating bounds check");
        p.functions[0].blocks[2]
            .instructions
            .push(Instruction::CheckIndex {
                index: 0,
                length: 2,
            });
        verify(&p).unwrap();
    }

    #[test]
    fn sparse_availability_handles_large_unused_universes_and_long_chains() {
        // Only value zero is live across edges. Materializing all possible
        // value/local ids as TOP for every block would need tens of millions
        // of tree entries, while the actual availability sets remain tiny.
        let count = 2048;
        let mut blocks: Vec<_> = (0..count)
            .map(|id| {
                block(
                    vec![],
                    if id + 1 == count {
                        Terminator::Return(0)
                    } else {
                        Terminator::Jump(id + 1)
                    },
                )
            })
            .collect();
        blocks[0].instructions.push(define(0, 7));
        let p = program(vec![Type::Num; 16384], vec![Type::Num; 16384], blocks);
        verify(&p).unwrap();
    }
}
