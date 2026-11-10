//! Recursive descent statements and Pratt expressions for the Vela 0.7 grammar.
use crate::lexer::{self, Line, Token, TokenKind};
use crate::model::*;

const MAX_NESTING: usize = 128;

/// Maximum expression construction steps per source line. Atoms, prefix/group
/// expressions, binary operators and calls each consume one step. This bounds
/// left-associative AST depth as well as recursive parser work, including when
/// an oversized partial AST must be dropped after a diagnostic.
pub const MAX_EXPRESSION_NODES: usize = 256;

pub fn parse(source: &str) -> Result<Program, Vec<Diagnostic>> {
    let lines = lexer::tokenize(source)?;
    let mut parser = Parser { lines, pos: 0 };
    let mut program = Program::default();
    let mut errors = Vec::new();
    while parser.pos < parser.lines.len() {
        let begin = parser.pos;
        let parsed = if parser.lines[parser.pos].depth == 0
            && parser.lines[parser.pos].tokens[0].is("record")
        {
            parser.record().map(|record| program.records.push(record))
        } else {
            parser
                .function()
                .map(|function| program.functions.push(function))
        };
        if let Err(error) = parsed {
            errors.push(error);
            // Recover at either declaration kind without manufacturing nested declarations.
            parser.pos = parser.pos.max(begin + 1);
            while parser.pos < parser.lines.len()
                && !(parser.lines[parser.pos].depth == 0
                    && (parser.lines[parser.pos].tokens[0].is("craft")
                        || parser.lines[parser.pos].tokens[0].is("record")))
            {
                parser.pos += 1;
            }
        }
    }
    if program.functions.is_empty() && program.records.is_empty() && errors.is_empty() {
        errors.push(Diagnostic::new(
            Span { line: 1, column: 1 },
            "source contains no declarations",
        ));
    }
    if errors.is_empty() {
        Ok(program)
    } else {
        Err(errors)
    }
}

struct Parser {
    lines: Vec<Line>,
    pos: usize,
}

impl Parser {
    fn record(&mut self) -> Result<RecordDecl, Diagnostic> {
        let line = self.lines[self.pos].clone();
        let mut cursor = Cursor::new(&line.tokens, line.span);
        cursor.expect("record")?;
        let (name, _) = cursor.name()?;
        cursor.expect(":")?;
        cursor.end()?;
        self.pos += 1;
        let mut fields = Vec::new();
        while let Some(field_line) = self.lines.get(self.pos) {
            if field_line.depth == 0 {
                break;
            }
            if field_line.depth != 1 {
                return Err(Diagnostic::new(
                    field_line.span,
                    "record fields require exactly four spaces of indentation",
                ));
            }
            if fields.len() >= MAX_RECORD_FIELDS {
                return Err(Diagnostic::new(
                    field_line.span,
                    format!("record field count exceeds compiler limit of {MAX_RECORD_FIELDS}"),
                ));
            }
            let mut field = Cursor::new(&field_line.tokens, field_line.span);
            let (name, span) = field.name()?;
            field.expect(":")?;
            let typ = field.typ()?;
            field.end()?;
            fields.push(FieldDecl { name, typ, span });
            self.pos += 1;
        }
        if fields.is_empty() {
            return Err(Diagnostic::new(
                line.span,
                "record requires at least one indented field",
            ));
        }
        Ok(RecordDecl {
            name,
            fields,
            span: line.span,
        })
    }
    fn function(&mut self) -> Result<Function, Diagnostic> {
        let line = self.lines[self.pos].clone();
        if line.depth != 0 || !line.tokens[0].is("craft") {
            return Err(Diagnostic::new(
                line.span,
                "expected top-level craft declaration",
            ));
        }
        let mut cursor = Cursor::new(&line.tokens, line.span);
        cursor.expect("craft")?;
        let (name, _) = cursor.name()?;
        cursor.expect("(")?;
        let mut params = Vec::new();
        if !cursor.is(")") {
            loop {
                let (name, span) = cursor.name()?;
                cursor.expect(":")?;
                let typ = cursor.typ()?;
                params.push(Param { name, typ, span });
                if !cursor.is(",") {
                    break;
                }
                cursor.expect(",")?;
            }
        }
        cursor.expect(")")?;
        cursor.expect("->")?;
        let returns = cursor.typ()?;
        cursor.expect(":")?;
        cursor.end()?;
        self.pos += 1;
        let body = self.block(1, line.span)?;
        Ok(Function {
            name,
            params,
            returns,
            body,
            span: line.span,
        })
    }

    fn block(&mut self, depth: usize, parent: Span) -> Result<Vec<Stmt>, Diagnostic> {
        if depth > MAX_NESTING {
            return Err(Diagnostic::new(
                parent,
                "block nesting exceeds compiler limit of 128",
            ));
        }
        let mut body = Vec::new();
        while self.pos < self.lines.len() {
            let line = self.lines[self.pos].clone();
            if line.depth < depth {
                break;
            }
            if line.depth > depth {
                return Err(Diagnostic::new(line.span, "unexpected indentation"));
            }
            let mut cursor = Cursor::new(&line.tokens, line.span);
            self.pos += 1;
            let kind = if cursor.is("when") || cursor.is("repeat") {
                let is_if = cursor.is("when");
                cursor.take()?;
                let condition = cursor.expr(0, 0)?;
                cursor.expect(":")?;
                cursor.end()?;
                let yes = self.block(depth + 1, line.span)?;
                if is_if {
                    let mut no = Vec::new();
                    if let Some(following) = self.lines.get(self.pos) {
                        if following.depth == depth && following.tokens[0].is("otherwise") {
                            let mut alt = Cursor::new(&following.tokens, following.span);
                            alt.expect("otherwise")?;
                            alt.expect(":")?;
                            alt.end()?;
                            let parent = following.span;
                            self.pos += 1;
                            no = self.block(depth + 1, parent)?;
                        }
                    }
                    StmtKind::If { condition, yes, no }
                } else {
                    StmtKind::While {
                        condition,
                        body: yes,
                    }
                }
            } else if cursor.is("keep") || cursor.is("change") {
                let mutable = cursor.is("change");
                cursor.take()?;
                let (name, _) = cursor.name()?;
                cursor.expect("=")?;
                let value = cursor.expr(0, 0)?;
                cursor.end()?;
                StmtKind::Let {
                    name,
                    mutable,
                    value,
                }
            } else if cursor.is("say") || cursor.is("give") {
                let is_return = cursor.is("give");
                cursor.take()?;
                let value = cursor.expr(0, 0)?;
                cursor.end()?;
                if is_return {
                    StmtKind::Return(value)
                } else {
                    StmtKind::Say(value)
                }
            } else if cursor.is("otherwise") {
                return Err(Diagnostic::new(
                    line.span,
                    "otherwise without matching when",
                ));
            } else {
                let (name, _) = cursor.name()?;
                let mut projections = Vec::new();
                loop {
                    if cursor.is(".") {
                        cursor.expression_step()?;
                        cursor.expect(".")?;
                        let (name, span) = cursor.name()?;
                        projections.push(Projection::Field { name, span });
                    } else if cursor.is("[") {
                        cursor.expression_step()?;
                        cursor.expect("[")?;
                        let index = cursor.expr(0, 0)?;
                        cursor.expect("]")?;
                        projections.push(Projection::Index(index));
                    } else {
                        break;
                    }
                }
                cursor.expect("=")?;
                let value = cursor.expr(0, 0)?;
                cursor.end()?;
                StmtKind::Assign {
                    place: Place { name, projections },
                    value,
                }
            };
            body.push(Stmt {
                kind,
                span: line.span,
            });
        }
        if body.is_empty() {
            return Err(Diagnostic::new(parent, "expected an indented statement"));
        }
        Ok(body)
    }
}

struct Cursor<'a> {
    tokens: &'a [Token],
    pos: usize,
    fallback: Span,
    expression_nodes: usize,
}

impl<'a> Cursor<'a> {
    fn new(tokens: &'a [Token], fallback: Span) -> Self {
        Self {
            tokens,
            pos: 0,
            fallback,
            expression_nodes: 0,
        }
    }
    fn span(&self) -> Span {
        self.tokens
            .get(self.pos)
            .map(|t| t.span)
            .unwrap_or(self.fallback)
    }
    fn is(&self, value: &str) -> bool {
        self.tokens.get(self.pos).is_some_and(|t| t.is(value))
    }
    fn take(&mut self) -> Result<Token, Diagnostic> {
        let token = self.tokens.get(self.pos).cloned().ok_or_else(|| {
            Diagnostic::new(
                self.span(),
                "unexpected end of line; expected expression or token",
            )
        })?;
        self.pos += 1;
        Ok(token)
    }
    fn expect(&mut self, value: &str) -> Result<(), Diagnostic> {
        if !self.is(value) {
            return Err(Diagnostic::new(self.span(), format!("expected '{value}'")));
        }
        self.pos += 1;
        Ok(())
    }
    fn end(&self) -> Result<(), Diagnostic> {
        if self.pos < self.tokens.len() {
            Err(Diagnostic::new(
                self.span(),
                "unexpected token after complete expression or header",
            ))
        } else {
            Ok(())
        }
    }
    fn name(&mut self) -> Result<(String, Span), Diagnostic> {
        let token = self.take()?;
        match token.kind {
            TokenKind::Word(name) if !reserved(&name) => Ok((name, token.span)),
            _ => Err(Diagnostic::new(
                token.span,
                "expected identifier; keywords cannot be used as names",
            )),
        }
    }
    fn typ(&mut self) -> Result<TypeSyntax, Diagnostic> {
        if self.is("[") {
            let span = self.take()?.span;
            if self.is("[") {
                return Err(Diagnostic::new(
                    self.span(),
                    "nested array types are not supported",
                ));
            }
            let element = match self.typ()? {
                TypeSyntax::Resolved(typ) => typ.scalar(),
                TypeSyntax::Named(_) => None,
            }
            .ok_or_else(|| Diagnostic::new(span, "array elements must have scalar type"))?;
            self.expect(";")?;
            let len = self.array_length()?;
            self.expect("]")?;
            return Ok(Type::Array(element, len).into());
        }
        if self.is("num") {
            self.take()?;
            return Ok(Type::Num.into());
        }
        if self.is("flag") {
            self.take()?;
            return Ok(Type::Flag.into());
        }
        if self.is("text") {
            self.take()?;
            return Ok(Type::Text.into());
        }
        if self.is("buffer") {
            self.take()?;
            return Ok(Type::Buffer.into());
        }
        let (mut name, _) = self.name()?;
        if self.is(".") {
            self.expect(".")?;
            let (member, _) = self.name()?;
            name.push('.');
            name.push_str(&member);
        }
        Ok(TypeSyntax::Named(name))
    }
    fn expr(&mut self, minimum: u8, depth: usize) -> Result<Expr, Diagnostic> {
        if depth >= MAX_NESTING {
            return Err(Diagnostic::new(
                self.span(),
                "expression nesting exceeds compiler limit of 128",
            ));
        }
        self.expression_step()?;
        let mut node = self.atom(depth)?;
        loop {
            if self.is(".") {
                self.expression_step()?;
                self.expect(".")?;
                let (name, span) = self.name()?;
                node = Expr {
                    kind: ExprKind::Field {
                        base: Box::new(node),
                        name,
                    },
                    span,
                };
                continue;
            }
            if self.is("{") {
                self.expression_step()?;
                let name = named_path(&node).ok_or_else(|| {
                    Diagnostic::new(
                        self.span(),
                        "record construction requires a named record type",
                    )
                })?;
                let fields = self.record_fields(depth)?;
                node.kind = ExprKind::Record { name, fields };
                continue;
            }
            if self.is("[") {
                self.expression_step()?;
                let index_span = self.take()?.span;
                let index = self.expr(0, depth + 1)?;
                self.expect("]")?;
                node = Expr {
                    kind: ExprKind::Index(Box::new(node), Box::new(index)),
                    span: index_span,
                };
                continue;
            }
            if self.is("(") {
                self.expression_step()?;
                let name = named_path(&node).ok_or_else(|| {
                    Diagnostic::new(
                        self.span(),
                        "only named functions and module-qualified functions are callable",
                    )
                })?;
                let args = self.arguments(depth)?;
                node.kind = ExprKind::Call(name, args);
                continue;
            }
            let Some((op, precedence)) = self.tokens.get(self.pos).and_then(binary) else {
                break;
            };
            if precedence < minimum {
                break;
            }
            self.expression_step()?;
            let op_span = self.take()?.span;
            let rhs = self.expr(precedence + 1, depth + 1)?;
            node = Expr {
                kind: ExprKind::Binary(op, Box::new(node), Box::new(rhs)),
                span: op_span,
            };
        }
        Ok(node)
    }

    // Keep recursive Pratt frames small: construction-specific vectors and
    // temporaries live in helpers only while that syntax is being parsed.
    fn atom(&mut self, depth: usize) -> Result<Expr, Diagnostic> {
        let token = self.take()?;
        let span = token.span;
        let kind = match token.kind {
            TokenKind::Integer(value) => {
                ExprKind::Literal(Literal::Num(value.parse::<i64>().map_err(|_| {
                    Diagnostic::new(span, "integer literal is outside signed 64-bit range")
                })?))
            }
            TokenKind::Text(value) => ExprKind::Literal(Literal::Text(value)),
            TokenKind::Word(ref word) if word == "true" || word == "false" => {
                ExprKind::Literal(Literal::Flag(word == "true"))
            }
            TokenKind::Symbol(ref symbol) if symbol == "-" => {
                if matches!(self.tokens.get(self.pos).map(|t| &t.kind), Some(TokenKind::Integer(value)) if value.parse::<u64>().ok() == Some(1u64 << 63))
                {
                    self.pos += 1;
                    ExprKind::Literal(Literal::Num(i64::MIN))
                } else {
                    ExprKind::Unary(Unary::Neg, Box::new(self.expr(6, depth + 1)?))
                }
            }
            TokenKind::Word(ref word) if word == "not" => {
                ExprKind::Unary(Unary::Not, Box::new(self.expr(6, depth + 1)?))
            }
            TokenKind::Word(ref word)
                if matches!(word.as_str(), "len" | "buffer" | "buffer_copy") =>
            {
                self.builtin(word, depth)?
            }
            TokenKind::Symbol(ref symbol) if symbol == "[" => self.array_literal(depth)?,
            TokenKind::Symbol(ref symbol) if symbol == "(" => {
                let expr = self.expr(0, depth + 1)?;
                self.expect(")")?;
                expr.kind
            }
            TokenKind::Word(name) if !reserved(&name) => ExprKind::Var(name),
            _ => return Err(Diagnostic::new(span, "expected expression")),
        };
        Ok(Expr { kind, span })
    }

    fn builtin(&mut self, name: &str, depth: usize) -> Result<ExprKind, Diagnostic> {
        self.expect("(")?;
        let value = Box::new(self.expr(0, depth + 1)?);
        self.expect(")")?;
        Ok(match name {
            "len" => ExprKind::Len(value),
            "buffer" => ExprKind::Buffer(value),
            "buffer_copy" => ExprKind::BufferCopy(value),
            _ => unreachable!("builtin keyword checked by atom"),
        })
    }

    fn array_literal(&mut self, depth: usize) -> Result<ExprKind, Diagnostic> {
        let mut elements = Vec::new();
        if !self.is("]") {
            loop {
                elements.push(self.expr(0, depth + 1)?);
                if !self.is(",") {
                    break;
                }
                self.expect(",")?;
            }
        }
        let kind = if elements.len() == 1 && self.is(";") {
            self.expect(";")?;
            let len = self.array_length()?;
            ExprKind::ArrayRepeat(Box::new(elements.pop().unwrap()), len)
        } else {
            ExprKind::Array(elements)
        };
        self.expect("]")?;
        Ok(kind)
    }

    fn record_fields(&mut self, depth: usize) -> Result<Vec<FieldValue>, Diagnostic> {
        self.expect("{")?;
        let mut fields = Vec::new();
        if !self.is("}") {
            loop {
                let (name, span) = self.name()?;
                self.expect(":")?;
                let value = self.expr(0, depth + 1)?;
                fields.push(FieldValue { name, value, span });
                if fields.len() > MAX_RECORD_FIELDS {
                    return Err(Diagnostic::new(self.span(), format!("record constructor field count exceeds compiler limit of {MAX_RECORD_FIELDS}")));
                }
                if !self.is(",") {
                    break;
                }
                self.expect(",")?;
            }
        }
        self.expect("}")?;
        Ok(fields)
    }

    fn arguments(&mut self, depth: usize) -> Result<Vec<Expr>, Diagnostic> {
        self.expect("(")?;
        let mut args = Vec::new();
        if !self.is(")") {
            loop {
                args.push(self.expr(0, depth + 1)?);
                if !self.is(",") {
                    break;
                }
                self.expect(",")?;
            }
        }
        self.expect(")")?;
        Ok(args)
    }
    fn expression_step(&mut self) -> Result<(), Diagnostic> {
        if self.expression_nodes >= MAX_EXPRESSION_NODES {
            return Err(Diagnostic::new(self.span(), format!("expression size exceeds compiler limit of {MAX_EXPRESSION_NODES} construction steps per line")));
        }
        self.expression_nodes += 1;
        Ok(())
    }
    fn array_length(&mut self) -> Result<usize, Diagnostic> {
        let token = self.take()?;
        match token.kind {
            TokenKind::Integer(value) => value
                .parse::<usize>()
                .ok()
                .filter(|len| (1..=MAX_ARRAY_LEN).contains(len)),
            _ => None,
        }
        .ok_or_else(|| {
            Diagnostic::new(
                token.span,
                format!("array length must be an integer literal from 1 to {MAX_ARRAY_LEN}"),
            )
        })
    }
}

// Fields on values and module names share postfix syntax; only a one-alias
// named path can subsequently become a function call or record constructor.
fn named_path(expr: &Expr) -> Option<String> {
    match &expr.kind {
        ExprKind::Var(name) => Some(name.clone()),
        ExprKind::Field { base, name } => match &base.kind {
            ExprKind::Var(module) => Some(format!("{module}.{name}")),
            _ => None,
        },
        _ => None,
    }
}

pub(crate) fn reserved(name: &str) -> bool {
    matches!(
        name,
        "craft"
            | "keep"
            | "change"
            | "when"
            | "otherwise"
            | "repeat"
            | "give"
            | "say"
            | "true"
            | "false"
            | "and"
            | "or"
            | "not"
            | "num"
            | "flag"
            | "text"
            | "use"
            | "as"
            | "len"
            | "record"
            | "buffer"
            | "buffer_copy"
    )
}

fn binary(token: &Token) -> Option<(Binary, u8)> {
    let word = match &token.kind {
        TokenKind::Word(word) | TokenKind::Symbol(word) => word.as_str(),
        _ => return None,
    };
    Some(match word {
        "or" => (Binary::Or, 1),
        "and" => (Binary::And, 2),
        "==" => (Binary::Eq, 3),
        "!=" => (Binary::Ne, 3),
        "<" => (Binary::Lt, 3),
        "<=" => (Binary::Le, 3),
        ">" => (Binary::Gt, 3),
        ">=" => (Binary::Ge, 3),
        "+" => (Binary::Add, 4),
        "-" => (Binary::Sub, 4),
        "*" => (Binary::Mul, 5),
        "/" => (Binary::Div, 5),
        "%" => (Binary::Rem, 5),
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    fn main(body: &str) -> Result<Program, Vec<Diagnostic>> {
        parse(&format!("craft main() -> num:\n{body}"))
    }

    #[test]
    fn parses_preserved_examples() {
        for source in [
            include_str!("../examples/hello.vela"),
            include_str!("../examples/loops.vela"),
            include_str!("../examples/fibonacci.vela"),
        ] {
            assert!(parse(source).is_ok());
        }
    }
    #[test]
    fn precedence_and_left_associativity() {
        let program = main("    give 10 - 3 - 2 * 2\n").unwrap();
        let StmtKind::Return(expr) = &program.functions[0].body[0].kind else {
            panic!()
        };
        let ExprKind::Binary(Binary::Sub, left, right) = &expr.kind else {
            panic!()
        };
        assert!(matches!(left.kind, ExprKind::Binary(Binary::Sub, _, _)));
        assert!(matches!(right.kind, ExprKind::Binary(Binary::Mul, _, _)));
    }
    #[test]
    fn accepts_i64_boundaries() {
        assert!(main("    say 9223372036854775807\n    give -9223372036854775808\n").is_ok());
        for value in [
            "9223372036854775808",
            "-9223372036854775809",
            "999999999999999999999999999",
        ] {
            assert!(main(&format!("    give {value}\n")).is_err());
        }
    }
    #[test]
    fn rejects_invalid_structure_and_names() {
        for source in [
            "craft main() -> num:\n",
            "craft keep() -> num:\n    give 0\n",
            "craft main() -> num:\n        give 0\n",
            "craft main() -> num:\n    otherwise:\n        give 0\n",
            "craft main() -> num:\n    keep true = 0\n    give 0\n",
            "craft main() -> num:\n    when true:\n    give 0\n",
            "craft main() -> num:\n    give f(1,)\n",
        ] {
            assert!(parse(source).is_err(), "{source}");
        }
    }
    #[test]
    fn synchronizes_between_functions() {
        let errors =
            parse("craft a( -> num:\n    give 0\ncraft b() num:\n    give 1\n").unwrap_err();
        assert_eq!(errors.len(), 2);
        assert_eq!(errors[1].span.line, 3);
    }
    #[test]
    fn limits_recursive_nesting() {
        let source = format!("    give {}0{}\n", "(".repeat(150), ")".repeat(150));
        assert!(main(&source).unwrap_err()[0].message.contains("nesting"));
    }
    #[test]
    fn limits_long_left_associative_expressions_before_ast_drop() {
        let source = format!("    give {}\n", vec!["1"; 10_000].join(" + "));
        let errors = main(&source).unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(errors[0].message.contains("expression size"));
    }
    #[test]
    fn respects_expression_budget_boundary() {
        // N literals and N-1 operators consume 2*N-1 steps.
        let largest = MAX_EXPRESSION_NODES.div_ceil(2);
        assert!(main(&format!("    give {}\n", vec!["1"; largest].join(" + "))).is_ok());
        assert!(main(&format!(
            "    give {}\n",
            vec!["1"; largest + 1].join(" + ")
        ))
        .is_err());
    }
    #[test]
    fn not_binds_more_tightly_than_comparison_as_in_prototype() {
        let program = main("    say not false == true\n    give 0\n").unwrap();
        let StmtKind::Say(expr) = &program.functions[0].body[0].kind else {
            panic!()
        };
        let ExprKind::Binary(Binary::Eq, left, _) = &expr.kind else {
            panic!()
        };
        assert!(matches!(left.kind, ExprKind::Unary(Unary::Not, _)));
    }
    #[test]
    fn parses_array_signatures_literals_and_element_assignment() {
        let program = parse("craft alter(a: [num; 3], b: [flag; 1]) -> [text; 2]:\n    change values = [1, 2, 3]\n    values[1 + 1] = a[0]\n    give [\"yes\", \"no\"]\n").unwrap();
        assert!(matches!(
            program.functions[0].params[0].typ,
            TypeSyntax::Resolved(Type::Array(ScalarType::Num, 3))
        ));
        assert!(matches!(
            program.functions[0].params[1].typ,
            TypeSyntax::Resolved(Type::Array(ScalarType::Flag, 1))
        ));
        assert!(matches!(
            program.functions[0].returns,
            TypeSyntax::Resolved(Type::Array(ScalarType::Text, 2))
        ));
        let StmtKind::Let { value, .. } = &program.functions[0].body[0].kind else {
            panic!()
        };
        assert!(matches!(&value.kind, ExprKind::Array(elements) if elements.len() == 3));
        let StmtKind::Assign { place, value } = &program.functions[0].body[1].kind else {
            panic!()
        };
        assert_eq!(place.name, "values");
        assert!(matches!(
            &place.projections[0],
            Projection::Index(Expr {
                kind: ExprKind::Binary(Binary::Add, _, _),
                ..
            })
        ));
        assert!(matches!(value.kind, ExprKind::Index(_, _)));
    }
    #[test]
    fn indexes_calls_and_literals_before_prefix_or_binary_operators() {
        let program =
            main("    say -math.make()[1] + len([2, 3]) * 4\n    give [7, 8][0]\n").unwrap();
        let StmtKind::Say(expr) = &program.functions[0].body[0].kind else {
            panic!()
        };
        let ExprKind::Binary(Binary::Add, left, right) = &expr.kind else {
            panic!()
        };
        let ExprKind::Unary(Unary::Neg, indexed) = &left.kind else {
            panic!()
        };
        let ExprKind::Index(call, _) = &indexed.kind else {
            panic!()
        };
        assert!(
            matches!(&call.kind, ExprKind::Call(name, args) if name == "math.make" && args.is_empty())
        );
        let ExprKind::Binary(Binary::Mul, length, _) = &right.kind else {
            panic!()
        };
        assert!(matches!(length.kind, ExprKind::Len(_)));
        let StmtKind::Return(expr) = &program.functions[0].body[1].kind else {
            panic!()
        };
        assert!(matches!(expr.kind, ExprKind::Index(_, _)));
    }
    #[test]
    fn rejects_malformed_arrays_indexing_and_length_calls() {
        for expr in [
            "[1,]",
            "[1 2]",
            "[",
            "a[]",
            "a[0",
            "len()",
            "len(1, 2)",
            "len",
        ] {
            assert!(
                main(&format!("    say {expr}\n    give 0\n")).is_err(),
                "{expr}"
            );
        }
        for statement in ["make()[0] = 2", "[1][0] = 2", "keep len = 1"] {
            assert!(
                main(&format!("    {statement}\n    give 0\n")).is_err(),
                "{statement}"
            );
        }
        // Empty-array inference and nested value types are semantic decisions.
        assert!(main("    keep values = []\n    give 0\n").is_ok());
    }
    #[test]
    fn array_type_lengths_are_bounded_integer_literals() {
        for length in [
            "0",
            "4097",
            "-1",
            "1 + 1",
            "size",
            "999999999999999999999999999999",
        ] {
            assert!(
                parse(&format!(
                    "craft f(a: [num; {length}]) -> num:\n    give 0\n"
                ))
                .is_err(),
                "{length}"
            );
        }
        assert!(parse("craft f(a: [num; 4096]) -> num:\n    give 0\n").is_ok());
        assert!(parse("craft f(a: [[num; 2]; 3]) -> num:\n    give 0\n").is_err());
    }
    #[test]
    fn repeat_array_literals_have_one_initializer_and_literal_length() {
        let program = main("    keep values = [make(7); 4096]\n    give 0\n").unwrap();
        let StmtKind::Let { value, .. } = &program.functions[0].body[0].kind else {
            panic!()
        };
        let ExprKind::ArrayRepeat(initializer, len) = &value.kind else {
            panic!()
        };
        assert_eq!(*len, 4096);
        assert!(
            matches!(&initializer.kind, ExprKind::Call(name, args) if name == "make" && args.len() == 1)
        );
        for expr in [
            "[1; 0]",
            "[1; 4097]",
            "[1; -1]",
            "[1; 2 + 1]",
            "[1; size]",
            "[1, 2; 3]",
            "[; 3]",
            "[1; 2,]",
        ] {
            assert!(
                main(&format!("    say {expr}\n    give 0\n")).is_err(),
                "{expr}"
            );
        }
    }
    #[test]
    fn array_postfix_and_literal_construction_obey_expression_budget() {
        let indexed = format!("values{}", "[0]".repeat(1000));
        assert!(
            main(&format!("    say {indexed}\n    give 0\n")).unwrap_err()[0]
                .message
                .contains("expression size")
        );
        let nested = format!("{}1{}", "[".repeat(150), "]".repeat(150));
        assert!(
            main(&format!("    say {nested}\n    give 0\n")).unwrap_err()[0]
                .message
                .contains("nesting")
        );
    }

    #[test]
    fn recursive_syntax_limits_fit_a_two_megabyte_parser_stack() {
        // The Windows main thread and ordinary test threads have small stacks.
        // Exercise accepted limits as well as rejection before recursion, using
        // a fixed small stack rather than depending on a developer's settings.
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                for (prefix, suffix) in [
                    ("[", "]"),
                    ("(", ")"),
                    ("not ", ""),
                    ("buffer(", ")"),
                    ("len(", ")"),
                    ("buffer_copy(", ")"),
                    ("f(", ")"),
                    ("R { value: ", " }"),
                    ("values[", "]"),
                ] {
                    let expression =
                        |count| format!("{}1{}", prefix.repeat(count), suffix.repeat(count));
                    assert!(
                        main(&format!(
                            "    say {}\n    give 0\n",
                            expression(MAX_NESTING - 1)
                        ))
                        .is_ok(),
                        "accepted boundary for {prefix:?}"
                    );
                    assert!(
                        main(&format!(
                            "    say {}\n    give 0\n",
                            expression(MAX_NESTING)
                        ))
                        .unwrap_err()[0]
                            .message
                            .contains("nesting"),
                        "rejection boundary for {prefix:?}"
                    );
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn records_allow_named_fields_forward_types_and_module_types() {
        let program = parse("record Container:\n    pair: Pair\n    samples: [num; 3]\n    remote: values.Tag\nrecord Pair:\n    left: num\n    right: flag\ncraft identity(value: Container) -> values.Tag:\n    give value.remote\n").unwrap();
        assert_eq!(program.records.len(), 2);
        assert_eq!(program.records[0].name, "Container");
        assert!(
            matches!(&program.records[0].fields[0].typ, TypeSyntax::Named(name) if name == "Pair")
        );
        assert!(
            matches!(&program.records[0].fields[2].typ, TypeSyntax::Named(name) if name == "values.Tag")
        );
        assert!(
            matches!(&program.functions[0].params[0].typ, TypeSyntax::Named(name) if name == "Container")
        );
        assert!(
            matches!(&program.functions[0].returns, TypeSyntax::Named(name) if name == "values.Tag")
        );
    }

    #[test]
    fn record_construction_preserves_source_order_and_postfix_fields() {
        let program = main("    keep p = shapes.Pair { right: mark(2), left: mark(1) }\n    say make().inner.samples[1] + (make()).left\n    give 0\n").unwrap();
        let StmtKind::Let { value, .. } = &program.functions[0].body[0].kind else {
            panic!()
        };
        let ExprKind::Record { name, fields } = &value.kind else {
            panic!()
        };
        assert_eq!(name, "shapes.Pair");
        assert_eq!(
            fields
                .iter()
                .map(|field| field.name.as_str())
                .collect::<Vec<_>>(),
            ["right", "left"]
        );
        assert_eq!(fields[0].span.line, 2);
        let StmtKind::Say(value) = &program.functions[0].body[1].kind else {
            panic!()
        };
        let ExprKind::Binary(Binary::Add, left, right) = &value.kind else {
            panic!()
        };
        assert!(
            matches!(&left.kind, ExprKind::Index(base, _) if matches!(&base.kind, ExprKind::Field { name, .. } if name == "samples"))
        );
        assert!(matches!(&right.kind, ExprKind::Field { name, .. } if name == "left"));
    }

    #[test]
    fn assignment_places_preserve_projection_order_and_spans() {
        let program = main("    value.inner.samples[index()] = 7\n    give 0\n").unwrap();
        let StmtKind::Assign { place, value } = &program.functions[0].body[0].kind else {
            panic!()
        };
        assert_eq!(place.name, "value");
        assert_eq!(place.projections.len(), 3);
        assert!(
            matches!(&place.projections[0], Projection::Field { name, span } if name == "inner" && span.column == 11)
        );
        assert!(
            matches!(&place.projections[1], Projection::Field { name, .. } if name == "samples")
        );
        assert!(
            matches!(&place.projections[2], Projection::Index(Expr { kind: ExprKind::Call(name, _), .. }) if name == "index")
        );
        assert!(matches!(value.kind, ExprKind::Literal(Literal::Num(7))));
        // The parser preserves a general place. Invalid type projections are
        // rejected semantically, rather than adding shape-specific grammar.
        assert!(main("    a[0].field[1] = 2\n    give 0\n").is_ok());
    }

    #[test]
    fn rejects_invalid_record_declarations_and_constructors() {
        for source in [
            "record Empty:\n",
            "record Bad:\n        x: num\n",
            "record Bad:\n    x num\n",
            "record Bad:\n    x: [Other; 2]\n",
            "craft record() -> num:\n    give 0\n",
            "record module.Bad:\n    x: num\n",
            "record Bad:\n    record Inner:\n        x: num\n",
        ] {
            assert!(parse(source).is_err(), "{source}");
        }
        for expression in [
            "Pair { x 1 }",
            "Pair { x: 1, }",
            "Pair { x: }",
            "Pair {",
            "make() { x: 1 }",
            "a.b.C { x: 1 }",
        ] {
            assert!(
                main(&format!("    keep p = {expression}\n    give 0\n")).is_err(),
                "{expression}"
            );
        }
        // Empty and duplicate construction fields are semantic diagnostics.
        assert!(
            main("    keep p = Pair {}\n    keep q = Pair { x: 1, x: 2 }\n    give 0\n").is_ok()
        );
    }

    #[test]
    fn recovers_between_both_declaration_kinds() {
        let errors = parse("record Bad:\n    x num\ncraft broken() num:\n    give 0\nrecord Other:\n    y:\ncraft fine() -> num:\n    give 0\n").unwrap_err();
        assert_eq!(
            errors
                .iter()
                .map(|error| error.span.line)
                .collect::<Vec<_>>(),
            [2, 3, 6]
        );
    }

    #[test]
    fn limits_record_fields_and_field_expression_construction() {
        let fields = |count: usize| {
            (0..count)
                .map(|index| format!("    field{index}: num\n"))
                .collect::<String>()
        };
        assert!(parse(&format!("record Full:\n{}", fields(MAX_RECORD_FIELDS))).is_ok());
        let full = (0..MAX_RECORD_FIELDS)
            .map(|index| format!("field{index}: 0"))
            .collect::<Vec<_>>()
            .join(", ");
        assert!(main(&format!("    keep full = Full {{ {full} }}\n    give 0\n")).is_ok());
        assert!(
            parse(&format!("record Full:\n{}", fields(MAX_RECORD_FIELDS + 1))).unwrap_err()[0]
                .message
                .contains("field count")
        );
        for statement in [
            format!("say a{}", ".field".repeat(10_000)),
            format!("a{} = 1", ".field".repeat(10_000)),
        ] {
            assert!(
                main(&format!("    {statement}\n    give 0\n")).unwrap_err()[0]
                    .message
                    .contains("expression size")
            );
        }
        let nested = format!("{}1{}", "Pair { x: ".repeat(150), " }".repeat(150));
        assert!(main(&format!("    keep p = {nested}\n    give 0\n")).is_err());
    }
}
