//! Structured IR to explicit control flow. Input must pass the structured verifier.
use super::*;
use crate::model::{IrExpr, IrExprKind, IrFunction, IrPlace, IrProjection, IrStmt};

/// Lower an already checked structured program without changing evaluation order.
pub fn lower(source: &IrProgram) -> Program {
    Program {
        functions: source
            .functions
            .iter()
            .map(|f| Builder::new(f, &source.records).finish(&f.body))
            .collect(),
        records: source.records.clone(),
        main: source.main,
    }
}

struct Builder<'a> {
    function: Function,
    records: &'a [IrRecord],
    current: Option<BlockId>,
}
impl<'a> Builder<'a> {
    fn new(source: &IrFunction, records: &'a [IrRecord]) -> Self {
        Self {
            function: Function {
                name: source.name.clone(),
                params: source.params.clone(),
                returns: source.returns,
                locals: source.locals.clone(),
                values: vec![],
                blocks: vec![],
                entry: 0,
            },
            records,
            current: None,
        }
    }
    fn finish(mut self, statements: &[IrStmt]) -> Function {
        let entry = self.block();
        self.function.entry = entry;
        self.current = Some(entry);
        self.statements(statements);
        self.function
    }
    fn block(&mut self) -> BlockId {
        let block = self.function.blocks.len();
        self.function.blocks.push(Block {
            instructions: vec![],
            terminator: Terminator::Unreachable,
        });
        block
    }
    fn value(&mut self, typ: Type) -> ValueId {
        let id = self.function.values.len();
        self.function.values.push(typ);
        id
    }
    fn emit(&mut self, instruction: Instruction) {
        self.function.blocks[self.current.expect("expression in a reachable block")]
            .instructions
            .push(instruction);
    }
    fn terminate(&mut self, terminator: Terminator) {
        let block = self.current.take().expect("terminating a live block");
        self.function.blocks[block].terminator = terminator;
    }
    fn define(&mut self, typ: Type, rvalue: Rvalue) -> ValueId {
        let value = self.value(typ);
        self.emit(Instruction::Define { value, rvalue });
        value
    }
    fn statements(&mut self, statements: &[IrStmt]) {
        for statement in statements {
            if self.current.is_none() {
                break;
            }
            match statement {
                IrStmt::Store(slot, expression) => {
                    let value = self.expression(expression);
                    self.emit(Instruction::StoreLocal { slot: *slot, value });
                }
                IrStmt::StorePlace { place, value } => {
                    // Checks are emitted as each index is evaluated, before RHS.
                    let place = self.place(place);
                    let value = self.expression(value);
                    self.emit(Instruction::StorePlace { place, value });
                }
                IrStmt::Say(expression) => {
                    let value = self.expression(expression);
                    self.emit(Instruction::Say(value));
                }
                IrStmt::Return(expression) => {
                    let value = self.expression(expression);
                    for slot in (0..self.function.locals.len()).rev() {
                        if self.function.locals[slot] == Type::Buffer {
                            self.emit(Instruction::DropLocal(slot));
                        }
                    }
                    self.terminate(Terminator::Return(value));
                }
                IrStmt::Drop(slot) => self.emit(Instruction::DropLocal(*slot)),
                IrStmt::BufferStore { slot, index, value } => {
                    let index = self.expression(index);
                    self.emit(Instruction::CheckBufferIndex { slot: *slot, index });
                    let value = self.expression(value);
                    self.emit(Instruction::BufferStore {
                        slot: *slot,
                        index,
                        value,
                    });
                }
                IrStmt::If { condition, yes, no } => {
                    let condition = self.expression(condition);
                    let yes_block = self.block();
                    let no_block = self.block();
                    self.terminate(Terminator::Branch {
                        condition,
                        yes: yes_block,
                        no: no_block,
                    });
                    self.current = Some(yes_block);
                    self.statements(yes);
                    let yes_end = self.current.take();
                    self.current = Some(no_block);
                    self.statements(no);
                    let no_end = self.current.take();
                    if yes_end.is_some() || no_end.is_some() {
                        let merge = self.block();
                        for end in [yes_end, no_end].into_iter().flatten() {
                            self.function.blocks[end].terminator = Terminator::Jump(merge);
                        }
                        self.current = Some(merge);
                    }
                }
                IrStmt::While { condition, body } => {
                    let header = self.block();
                    let body_block = self.block();
                    let exit = self.block();
                    self.terminate(Terminator::Jump(header));
                    self.current = Some(header);
                    let condition = self.expression(condition);
                    self.terminate(Terminator::Branch {
                        condition,
                        yes: body_block,
                        no: exit,
                    });
                    self.current = Some(body_block);
                    self.statements(body);
                    if self.current.is_some() {
                        self.terminate(Terminator::Jump(header));
                    }
                    self.current = Some(exit);
                }
            }
        }
    }
    fn place(&mut self, source: &IrPlace) -> Place {
        let mut typ = self.function.locals[source.slot];
        let mut projections = vec![];
        for projection in &source.projections {
            match projection {
                IrProjection::Field(field) => {
                    let Type::Record { id, .. } = typ else {
                        unreachable!("checked record place")
                    };
                    typ = self.records[id].fields[*field].typ;
                    projections.push(Projection::Field(*field));
                }
                IrProjection::Index(index) => {
                    let Type::Array(element, length) = typ else {
                        unreachable!("checked array place")
                    };
                    let index = self.expression(index);
                    self.emit(Instruction::CheckIndex { index, length });
                    projections.push(Projection::Index(index));
                    typ = element.typ();
                }
            }
        }
        Place {
            slot: source.slot,
            projections,
        }
    }
    /// Private local field paths have no effects and can be read without copies
    /// of their containing record. Array indices are handled by the caller.
    fn direct_place(expression: &IrExpr) -> Option<Place> {
        match &expression.kind {
            IrExprKind::Local(slot) => Some(Place {
                slot: *slot,
                projections: vec![],
            }),
            IrExprKind::Field { base, field } => {
                let mut place = Self::direct_place(base)?;
                place.projections.push(Projection::Field(*field));
                Some(place)
            }
            _ => None,
        }
    }
    fn expression(&mut self, expression: &IrExpr) -> ValueId {
        let rvalue = match &expression.kind {
            IrExprKind::Literal(value) => Rvalue::Literal(value.clone()),
            IrExprKind::Local(slot) if expression.typ == Type::Buffer => Rvalue::TakeLocal(*slot),
            IrExprKind::Local(slot) => Rvalue::LoadLocal(*slot),
            IrExprKind::Buffer(length) => Rvalue::Buffer(self.expression(length)),
            IrExprKind::BufferCopy { slot } => Rvalue::BufferCopy(*slot),
            IrExprKind::BufferLen { slot } => Rvalue::BufferLen(*slot),
            IrExprKind::BufferGet { slot, index } => {
                let index = self.expression(index);
                self.emit(Instruction::CheckBufferIndex { slot: *slot, index });
                Rvalue::BufferGet { slot: *slot, index }
            }
            IrExprKind::Unary(operator, value) => {
                let value = self.expression(value);
                Rvalue::Unary(*operator, value)
            }
            IrExprKind::Binary(operator @ (Binary::And | Binary::Or), left, right) => {
                let result = self.value(Type::Flag);
                let left = self.expression(left);
                let short = self.block();
                let rhs = self.block();
                let merge = self.block();
                let (yes, no) = if *operator == Binary::And {
                    (rhs, short)
                } else {
                    (short, rhs)
                };
                self.terminate(Terminator::Branch {
                    condition: left,
                    yes,
                    no,
                });
                self.current = Some(short);
                self.emit(Instruction::Define {
                    value: result,
                    rvalue: Rvalue::Use(left),
                });
                self.terminate(Terminator::Jump(merge));
                self.current = Some(rhs);
                let right = self.expression(right);
                self.emit(Instruction::Define {
                    value: result,
                    rvalue: Rvalue::Use(right),
                });
                self.terminate(Terminator::Jump(merge));
                self.current = Some(merge);
                return result;
            }
            IrExprKind::Binary(operator, left, right) => {
                let left = self.expression(left);
                let right = self.expression(right);
                Rvalue::Binary(*operator, left, right)
            }
            IrExprKind::Call(function, args) => {
                Rvalue::Call(*function, args.iter().map(|a| self.expression(a)).collect())
            }
            IrExprKind::Array(elements) => {
                Rvalue::Array(elements.iter().map(|e| self.expression(e)).collect())
            }
            IrExprKind::ArrayRepeat(value, length) => {
                let value = self.expression(value);
                Rvalue::ArrayRepeat(value, *length)
            }
            IrExprKind::Record { record, fields } => Rvalue::Record {
                record: *record,
                fields: fields
                    .iter()
                    .map(|(field, value)| (*field, self.expression(value)))
                    .collect(),
            },
            IrExprKind::Field { base, field } => {
                if let Some(place) = Self::direct_place(expression) {
                    Rvalue::ReadPlace(place)
                } else {
                    let base = self.expression(base);
                    Rvalue::Field {
                        base,
                        field: *field,
                    }
                }
            }
            IrExprKind::Index(base, index) => {
                let Type::Array(_, length) = base.typ else {
                    unreachable!("checked array read")
                };
                if let Some(mut place) = Self::direct_place(base) {
                    let index = self.expression(index);
                    self.emit(Instruction::CheckIndex { index, length });
                    place.projections.push(Projection::Index(index));
                    Rvalue::ReadPlace(place)
                } else {
                    let base = self.expression(base);
                    let index = self.expression(index);
                    self.emit(Instruction::CheckIndex { index, length });
                    Rvalue::Index { base, index }
                }
            }
            IrExprKind::Len(array) => {
                let Type::Array(_, length) = array.typ else {
                    unreachable!("checked len")
                };
                if Self::direct_place(array).is_some() {
                    Rvalue::Literal(Literal::Num(length as i64))
                } else {
                    let value = self.expression(array);
                    Rvalue::Len(value)
                }
            }
        };
        self.define(expression.typ, rvalue)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn graph(body: &str) -> Program {
        lower(&crate::compile(&format!("craft main() -> num:\n{body}"), false).unwrap())
    }
    #[test]
    fn short_circuit_is_control_flow_with_initialized_merge() {
        let graph = graph("    say false and (1 / 0 == 0)\n    give 0\n");
        super::super::verify(&graph).unwrap();
        assert_eq!(graph.functions[0].blocks.len(), 4);
        assert!(matches!(
            graph.functions[0].blocks[0].terminator,
            Terminator::Branch { .. }
        ));
        assert!(!graph.functions[0].blocks[0]
            .instructions
            .iter()
            .any(|i| matches!(
                i,
                Instruction::Define {
                    rvalue: Rvalue::Binary(Binary::Div, ..),
                    ..
                }
            )));
    }
    #[test]
    fn nested_branches_loops_and_returns_have_explicit_edges() {
        let graph=graph("    change i = 0\n    repeat i < 4:\n        when i == 2:\n            give i\n        otherwise:\n            i = i + 1\n    give 0\n");
        super::super::verify(&graph).unwrap();
        assert!(graph.functions[0]
            .blocks
            .iter()
            .any(|b| matches!(b.terminator, Terminator::Jump(_))));
    }
    #[test]
    fn projected_checks_precede_rhs_and_local_reads_avoid_snapshots() {
        let ir=crate::compile("record Data:\n    items: [num; 2]\ncraft rhs() -> num:\n    say 9\n    give 7\ncraft main() -> num:\n    change d = Data { items: [1, 2] }\n    d.items[2] = rhs()\n    say d.items[0]\n    give 0\n",false).unwrap();
        let graph = lower(&ir);
        super::super::verify(&graph).unwrap();
        let ops = &graph.functions[graph.main].blocks[0].instructions;
        let check = ops
            .iter()
            .position(|i| matches!(i, Instruction::CheckIndex { .. }))
            .unwrap();
        let call = ops
            .iter()
            .position(|i| {
                matches!(
                    i,
                    Instruction::Define {
                        rvalue: Rvalue::Call(..),
                        ..
                    }
                )
            })
            .unwrap();
        assert!(check < call);
        assert!(ops.iter().any(|i| matches!(
            i,
            Instruction::Define {
                rvalue: Rvalue::ReadPlace(_),
                ..
            }
        )));
        assert!(!ops.iter().any(|i| matches!(
            i,
            Instruction::Define {
                rvalue: Rvalue::LoadLocal(_),
                ..
            }
        )));
    }
    #[test]
    fn len_of_call_keeps_call_and_literal_initializer_effects() {
        let ir=crate::compile("craft make() -> [num; 1]:\n    say 7\n    give [1]\ncraft main() -> num:\n    say len(make())\n    say len([1 / 0; 2])\n    give 0\n",false).unwrap();
        let graph = lower(&ir);
        super::super::verify(&graph).unwrap();
        let ops = &graph.functions[graph.main].blocks[0].instructions;
        assert!(ops.iter().any(|i| matches!(
            i,
            Instruction::Define {
                rvalue: Rvalue::Call(..),
                ..
            }
        )));
        assert!(ops.iter().any(|i| matches!(
            i,
            Instruction::Define {
                rvalue: Rvalue::Binary(Binary::Div, ..),
                ..
            }
        )));
    }
}
