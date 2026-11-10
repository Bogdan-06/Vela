//! Conservative, checked constant folding on typed structured IR.
//! Faulting arithmetic stays in the IR so optimization preserves runtime faults.
use crate::model::*;

pub fn run(program: &mut IrProgram) {
    for function in &mut program.functions {
        block(&mut function.body);
    }
}
fn block(stmts: &mut Vec<IrStmt>) {
    let old = std::mem::take(stmts);
    for mut stmt in old {
        match &mut stmt {
            IrStmt::Drop(_) => {}
            IrStmt::BufferStore { index, value, .. } => {
                fold(index);
                fold(value);
            }
            IrStmt::Store(_, value) | IrStmt::Say(value) | IrStmt::Return(value) => fold(value),
            IrStmt::StorePlace { place, value } => {
                for projection in &mut place.projections {
                    if let IrProjection::Index(index) = projection {
                        fold(index);
                    }
                }
                fold(value);
            }
            IrStmt::If { condition, yes, no } => {
                fold(condition);
                block(yes);
                block(no);
                if let IrExprKind::Literal(Literal::Flag(test)) = condition.kind {
                    stmts.extend(if test {
                        std::mem::take(yes)
                    } else {
                        std::mem::take(no)
                    });
                    if stmts.last().is_some_and(terminates) {
                        break;
                    }
                    continue;
                }
            }
            IrStmt::While { condition, body } => {
                fold(condition);
                block(body);
                if matches!(condition.kind, IrExprKind::Literal(Literal::Flag(false))) {
                    continue;
                }
            }
        }
        let stop = terminates(&stmt);
        stmts.push(stmt);
        if stop {
            break;
        }
    }
}
fn terminates(stmt: &IrStmt) -> bool {
    match stmt {
        IrStmt::Return(_) => true,
        IrStmt::If { yes, no, .. } => {
            yes.last().is_some_and(terminates) && no.last().is_some_and(terminates)
        }
        _ => false,
    }
}
fn fold(expr: &mut IrExpr) {
    let value = match &mut expr.kind {
        IrExprKind::Unary(op, child) => {
            fold(child);
            match (*op, &child.kind) {
                (Unary::Neg, IrExprKind::Literal(Literal::Num(x))) => {
                    x.checked_neg().map(Literal::Num)
                }
                (Unary::Not, IrExprKind::Literal(Literal::Flag(x))) => Some(Literal::Flag(!x)),
                _ => None,
            }
        }
        IrExprKind::Binary(op, left, right) => {
            fold(left);
            // Discarding the RHS is legal only if it cannot be evaluated.
            match (*op, &left.kind) {
                (Binary::And, IrExprKind::Literal(Literal::Flag(false))) => {
                    Some(Literal::Flag(false))
                }
                (Binary::Or, IrExprKind::Literal(Literal::Flag(true))) => Some(Literal::Flag(true)),
                _ => {
                    fold(right);
                    if let (IrExprKind::Literal(a), IrExprKind::Literal(b)) =
                        (&left.kind, &right.kind)
                    {
                        binary(*op, a, b)
                    } else {
                        None
                    }
                }
            }
        }
        IrExprKind::Call(_, args) | IrExprKind::Array(args) => {
            for arg in args {
                fold(arg);
            }
            None
        }
        IrExprKind::Record { fields, .. } => {
            for (_, value) in fields {
                fold(value);
            }
            None
        }
        IrExprKind::Field { base, .. } => {
            fold(base);
            None
        }
        IrExprKind::Index(array, index) => {
            fold(array);
            fold(index);
            None
        }
        // Length is statically known, but evaluating its array operand can call
        // functions, print output or fault while constructing array elements.
        IrExprKind::Len(array) | IrExprKind::ArrayRepeat(array, _) | IrExprKind::Buffer(array) => {
            fold(array);
            None
        }
        IrExprKind::BufferGet { index, .. } => {
            fold(index);
            None
        }
        _ => None,
    };
    if let Some(value) = value {
        expr.kind = IrExprKind::Literal(value);
    }
}
fn binary(op: Binary, a: &Literal, b: &Literal) -> Option<Literal> {
    use Binary::*;
    match (a, b) {
        (Literal::Num(a), Literal::Num(b)) => Some(match op {
            Add => Literal::Num(a.checked_add(*b)?),
            Sub => Literal::Num(a.checked_sub(*b)?),
            Mul => Literal::Num(a.checked_mul(*b)?),
            Div => Literal::Num(a.checked_div(*b)?),
            Rem => Literal::Num(a.checked_rem(*b)?),
            Eq => Literal::Flag(a == b),
            Ne => Literal::Flag(a != b),
            Lt => Literal::Flag(a < b),
            Le => Literal::Flag(a <= b),
            Gt => Literal::Flag(a > b),
            Ge => Literal::Flag(a >= b),
            _ => return None,
        }),
        (Literal::Flag(a), Literal::Flag(b)) => Some(Literal::Flag(match op {
            And => *a && *b,
            Or => *a || *b,
            Eq => a == b,
            Ne => a != b,
            _ => return None,
        })),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn expr(source: &str) -> IrExpr {
        let program = crate::compile(
            &format!("craft main() -> num:\n    say {source}\n    give 0\n"),
            true,
        )
        .unwrap();
        match &program.functions[0].body[0] {
            IrStmt::Say(expr) => expr.clone(),
            _ => panic!("expected say"),
        }
    }
    #[test]
    fn constants_fold() {
        assert!(matches!(
            expr("2 + 3 * 4").kind,
            IrExprKind::Literal(Literal::Num(14))
        ));
    }
    #[test]
    fn fault_not_folded() {
        assert!(matches!(
            expr("9223372036854775807 + 1").kind,
            IrExprKind::Binary(Binary::Add, _, _)
        ));
        assert!(matches!(
            expr("1 / 0").kind,
            IrExprKind::Binary(Binary::Div, _, _)
        ));
    }
    #[test]
    fn short_circuit_preserved() {
        assert!(matches!(
            expr("false and (1 / 0 == 0)").kind,
            IrExprKind::Literal(Literal::Flag(false))
        ));
    }

    #[test]
    fn array_length_preserves_operand_evaluation_and_faults() {
        let value = expr("len([1 / 0; 4])");
        let IrExprKind::Len(array) = value.kind else {
            panic!("len must evaluate its operand")
        };
        let IrExprKind::ArrayRepeat(value, 4) = array.kind else {
            panic!("repeat initializer must not be expanded")
        };
        assert!(matches!(value.kind, IrExprKind::Binary(Binary::Div, _, _)));
        let value = expr("[1 + 2, 3 * 4][0]");
        let IrExprKind::Index(array, _) = value.kind else {
            panic!("index bounds/evaluation must remain")
        };
        let IrExprKind::Array(values) = array.kind else {
            panic!()
        };
        assert!(matches!(
            values[0].kind,
            IrExprKind::Literal(Literal::Num(3))
        ));
        assert!(matches!(
            values[1].kind,
            IrExprKind::Literal(Literal::Num(12))
        ));
    }
}
