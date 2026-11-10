//! Name resolution, lexical scopes, static typing and control-flow validation.
//!
//! A successful check produces a typed, structured IR. Local slots are unique
//! within each function, including bindings in separate lexical scopes.
use crate::model::*;
use std::collections::HashMap;

#[derive(Clone)]
struct Signature {
    index: usize,
    params: Vec<Type>,
    returns: Type,
}

#[derive(Clone, Copy)]
struct Binding {
    slot: usize,
    typ: Type,
    mutable: bool,
}

/// Resolve nominal record layouts before resolving function signatures.
struct Layouts<'a> {
    declarations: &'a [RecordDecl],
    ids: HashMap<String, usize>,
    values: Vec<Option<IrRecord>>,
    heights: Vec<usize>,
    states: Vec<u8>,
    active: Vec<usize>,
    errors: Vec<Diagnostic>,
}
impl Layouts<'_> {
    fn visit(&mut self, id: usize) -> Option<Type> {
        match self.states[id] {
            2 => {
                return self.values[id].as_ref().map(|record| Type::Record {
                    id,
                    words: record.words,
                })
            }
            3 => return None,
            1 => {
                let mut chain: Vec<_> = self
                    .active
                    .iter()
                    .map(|&id| self.declarations[id].name.as_str())
                    .collect();
                chain.push(&self.declarations[id].name);
                self.errors.push(Diagnostic::new(
                    self.declarations[id].span,
                    format!("record layout cycle: {}", chain.join(" -> ")),
                ));
                return None;
            }
            _ => {}
        }
        if self.active.len() >= MAX_RECORD_DEPTH {
            self.errors.push(Diagnostic::new(
                self.declarations[id].span,
                format!("record nesting exceeds compiler limit of {MAX_RECORD_DEPTH}"),
            ));
            return None;
        }
        self.states[id] = 1;
        self.active.push(id);
        let declaration = &self.declarations[id];
        let mut fields = Vec::new();
        let mut names = std::collections::HashSet::new();
        let mut words = 0usize;
        let mut height = 1usize;
        let mut valid = true;
        if !(1..=MAX_RECORD_FIELDS).contains(&declaration.fields.len()) {
            self.errors.push(Diagnostic::new(
                declaration.span,
                format!("record requires 1..={MAX_RECORD_FIELDS} fields"),
            ));
            valid = false;
        }
        for field in &declaration.fields {
            if !names.insert(field.name.clone()) {
                self.errors.push(Diagnostic::new(
                    field.span,
                    format!(
                        "duplicate field '{}' in record '{}'",
                        field.name, declaration.name
                    ),
                ));
                valid = false;
            }
            let typ = match &field.typ {
                TypeSyntax::Resolved(typ) => valid_source_type(*typ, field.span, &mut self.errors),
                TypeSyntax::Named(name) => match self.ids.get(name).copied() {
                    Some(target) => self.visit(target),
                    None => {
                        self.errors.push(Diagnostic::new(
                            field.span,
                            format!("unknown record type '{name}'"),
                        ));
                        None
                    }
                },
            };
            if let Some(typ) = typ {
                if typ == Type::Buffer {
                    self.errors.push(Diagnostic::new(
                        field.span,
                        "owned buffer fields are not supported; keep buffers in separate local bindings",
                    ));
                    valid = false;
                }
                if let Type::Record { id: child, .. } = typ {
                    height = height.max(self.heights[child] + 1);
                }
                let offset = words;
                match words.checked_add(typ.words()) {
                    Some(next) if next <= MAX_RECORD_WORDS => words = next,
                    _ => {
                        self.errors.push(Diagnostic::new(
                            field.span,
                            format!(
                                "record layout exceeds compiler limit of {MAX_RECORD_WORDS} words"
                            ),
                        ));
                        valid = false;
                    }
                }
                fields.push(IrField {
                    name: field.name.clone(),
                    typ,
                    offset,
                });
            } else {
                valid = false;
            }
        }
        if height > MAX_RECORD_DEPTH {
            self.errors.push(Diagnostic::new(
                declaration.span,
                format!("record nesting exceeds compiler limit of {MAX_RECORD_DEPTH}"),
            ));
            valid = false;
        }
        self.active.pop();
        if valid {
            self.heights[id] = height;
            self.values[id] = Some(IrRecord {
                name: declaration.name.clone(),
                fields,
                words,
            });
            self.states[id] = 2;
            Some(Type::Record { id, words })
        } else {
            self.states[id] = 3;
            None
        }
    }
}
fn valid_source_type(typ: Type, span: Span, errors: &mut Vec<Diagnostic>) -> Option<Type> {
    match typ {
        Type::Array(_, length) if !(1..=MAX_ARRAY_LEN).contains(&length) => {
            errors.push(Diagnostic::new(
                span,
                format!("array length must be between 1 and {MAX_ARRAY_LEN}"),
            ));
            None
        }
        Type::Record { .. } => {
            errors.push(Diagnostic::new(
                span,
                "record annotations must use a named source type",
            ));
            None
        }
        _ => Some(typ),
    }
}
fn resolve_annotation(
    syntax: &TypeSyntax,
    span: Span,
    ids: &HashMap<String, usize>,
    records: &[IrRecord],
    errors: &mut Vec<Diagnostic>,
) -> Type {
    match syntax {
        TypeSyntax::Resolved(typ) => valid_source_type(*typ, span, errors).unwrap_or(Type::Num),
        TypeSyntax::Named(name) => match ids.get(name).copied() {
            Some(id) => Type::Record {
                id,
                words: records[id].words,
            },
            None => {
                errors.push(Diagnostic::new(
                    span,
                    format!("unknown record type '{name}'"),
                ));
                Type::Num
            }
        },
    }
}
fn type_name(typ: Type, records: &[IrRecord]) -> String {
    match typ {
        Type::Record { id, .. } => records
            .get(id)
            .map(|r| r.name.clone())
            .unwrap_or_else(|| typ.to_string()),
        _ => typ.to_string(),
    }
}

/// Resolve and type-check the complete program before any native code is emitted.
pub fn check(program: Program) -> Result<IrProgram, Vec<Diagnostic>> {
    let mut errors = Vec::new();
    if program.records.len() > MAX_RECORD_TYPES {
        return Err(vec![Diagnostic::new(
            program.records[MAX_RECORD_TYPES].span,
            format!("record count exceeds compiler limit of {MAX_RECORD_TYPES}"),
        )]);
    }
    let mut ids = HashMap::new();
    for (id, record) in program.records.iter().enumerate() {
        if ids.insert(record.name.clone(), id).is_some() {
            errors.push(Diagnostic::new(
                record.span,
                format!("duplicate record '{}'", record.name),
            ));
        }
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    let mut layout = Layouts {
        declarations: &program.records,
        ids,
        values: vec![None; program.records.len()],
        heights: vec![0; program.records.len()],
        states: vec![0; program.records.len()],
        active: vec![],
        errors: vec![],
    };
    for id in 0..program.records.len() {
        layout.visit(id);
    }
    if !layout.errors.is_empty() {
        return Err(layout.errors);
    }
    let records: Vec<_> = layout.values.into_iter().map(Option::unwrap).collect();
    let ids = layout.ids;
    let mut signatures = HashMap::new();
    let mut resolved = Vec::new();
    for (index, function) in program.functions.iter().enumerate() {
        if ids.contains_key(&function.name) {
            errors.push(Diagnostic::new(
                function.span,
                format!(
                    "function '{}' conflicts with a record declaration",
                    function.name
                ),
            ));
        }
        let signature = Signature {
            index,
            params: function
                .params
                .iter()
                .map(|p| resolve_annotation(&p.typ, p.span, &ids, &records, &mut errors))
                .collect(),
            returns: resolve_annotation(
                &function.returns,
                function.span,
                &ids,
                &records,
                &mut errors,
            ),
        };
        if signatures.contains_key(&function.name) {
            errors.push(Diagnostic::new(
                function.span,
                format!("duplicate function '{}'", function.name),
            ));
        } else {
            signatures.insert(function.name.clone(), signature.clone());
        }
        if function.params.len() > 6 {
            errors.push(Diagnostic::new(
                function.span,
                "functions support at most six parameters",
            ));
        }
        resolved.push(signature);
    }
    let main = match signatures.get("main") {
        Some(signature) if signature.params.is_empty() && signature.returns == Type::Num => {
            signature.index
        }
        _ => {
            let span = program
                .functions
                .iter()
                .find(|f| f.name == "main")
                .or(program.functions.first())
                .map(|f| f.span)
                .unwrap_or(Span { line: 1, column: 1 });
            errors.push(Diagnostic::new(
                span,
                "entry point must be craft main() -> num:",
            ));
            0
        }
    };
    let mut functions = Vec::new();
    for (function, signature) in program.functions.into_iter().zip(resolved) {
        let mut checker = Checker {
            signatures: &signatures,
            records: &records,
            record_ids: &ids,
            errors: &mut errors,
            scopes: vec![HashMap::new()],
            locals: Vec::new(),
            owner_moves: Vec::new(),
            declarations: Vec::new(),
            returns: signature.returns,
        };
        for (parameter, typ) in function.params.iter().zip(&signature.params) {
            checker.declare(&parameter.name, *typ, false, parameter.span);
        }
        let (body, returns) = checker.block(&function.body, false);
        if !returns {
            checker.error(
                function.span,
                format!(
                    "function '{}' does not return a value on every path; add give",
                    function.name
                ),
            );
        }
        let ir_function = IrFunction {
            name: function.name,
            params: signature.params,
            returns: signature.returns,
            locals: checker.locals,
            body,
        };
        if let Err(message) = crate::ir::frame_words(&ir_function) {
            errors.push(Diagnostic::new(function.span, message));
        }
        functions.push(ir_function);
    }
    if errors.is_empty() {
        Ok(IrProgram {
            functions,
            records,
            main,
        })
    } else {
        Err(errors)
    }
}

struct Checker<'a> {
    signatures: &'a HashMap<String, Signature>,
    records: &'a [IrRecord],
    record_ids: &'a HashMap<String, usize>,
    errors: &'a mut Vec<Diagnostic>,
    scopes: Vec<HashMap<String, Binding>>,
    locals: Vec<Type>,
    /// None means definitely available; Some records a consuming source use on
    /// at least one incoming path. Non-resource slots are ignored.
    owner_moves: Vec<Option<Span>>,
    declarations: Vec<(String, Span)>,
    returns: Type,
}

impl Checker<'_> {
    fn error(&mut self, span: Span, message: impl Into<String>) {
        self.errors.push(Diagnostic::new(span, message));
    }

    fn declare(&mut self, name: &str, typ: Type, mutable: bool, span: Span) -> Option<usize> {
        if self
            .scopes
            .last()
            .is_some_and(|scope| scope.contains_key(name))
        {
            self.error(
                span,
                format!("'{}' is already declared in this scope", name),
            );
            return None;
        }
        let slot = self.locals.len();
        self.locals.push(typ);
        self.owner_moves.push(None);
        self.declarations.push((name.to_owned(), span));
        self.scopes
            .last_mut()?
            .insert(name.to_owned(), Binding { slot, typ, mutable });
        Some(slot)
    }

    fn binding(&self, name: &str) -> Option<Binding> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }

    fn require(&mut self, expr: &IrExpr, wanted: Type, context: &str) {
        if expr.typ != wanted {
            self.error(
                expr.span,
                format!(
                    "{} expects {}, got {}",
                    context,
                    type_name(wanted, self.records),
                    type_name(expr.typ, self.records)
                ),
            );
        }
    }

    fn available(&mut self, slot: usize, span: Span) -> bool {
        if self.owner_moves[slot].is_some() {
            let name = &self.declarations[slot].0;
            self.owner_error(slot, span, format!(
                "buffer '{name}' is unavailable after a move on this or another path; use buffer_copy before moving it or reinitialize a change binding",
            ));
            false
        } else {
            true
        }
    }

    fn owner_error(&mut self, slot: usize, span: Span, message: impl Into<String>) {
        let mut diagnostic = Diagnostic::new(span, message);
        if let Some(moved) = self.owner_moves[slot] {
            diagnostic = diagnostic.with_related(moved, "buffer moved here on an incoming path");
        }
        diagnostic = diagnostic.with_related(self.declarations[slot].1, "buffer declared here");
        self.errors.push(diagnostic);
    }

    fn restore_owners(&mut self, snapshot: &[Option<Span>]) {
        self.owner_moves[..snapshot.len()].copy_from_slice(snapshot);
    }

    fn join_owners(&mut self, left: &[Option<Span>], right: &[Option<Span>]) {
        for (slot, (left, right)) in left.iter().zip(right).enumerate() {
            self.owner_moves[slot] = left.or(*right);
        }
    }

    /// Buffer inspection never creates an escaping reference or an implicit
    /// owner copy. Restrict it to a named local until general borrows exist.
    fn buffer_local(&mut self, expr: &Expr, context: &str) -> Option<usize> {
        let ExprKind::Var(name) = &expr.kind else {
            self.error(
                expr.span,
                format!("{context} requires a named buffer local; bind the value first"),
            );
            return None;
        };
        let Some(binding) = self.binding(name) else {
            self.error(expr.span, format!("unknown variable '{name}'"));
            return None;
        };
        if binding.typ != Type::Buffer {
            self.error(
                expr.span,
                format!(
                    "{context} expects buffer, got {}",
                    type_name(binding.typ, self.records)
                ),
            );
            return None;
        }
        self.available(binding.slot, expr.span);
        Some(binding.slot)
    }

    fn block(&mut self, statements: &[Stmt], nested: bool) -> (Vec<IrStmt>, bool) {
        if nested {
            self.scopes.push(HashMap::new());
        }
        let mut output = Vec::new();
        let mut returns = false;
        for statement in statements {
            if returns {
                self.error(
                    statement.span,
                    "unreachable statement after unconditional return",
                );
            }
            match &statement.kind {
                StmtKind::Let {
                    name,
                    mutable,
                    value,
                } => {
                    if let Some(value) = self.expr(value) {
                        if let Some(slot) = self.declare(name, value.typ, *mutable, statement.span)
                        {
                            output.push(IrStmt::Store(slot, value));
                        }
                    }
                }
                StmtKind::Assign { place, value } => {
                    let binding = self.binding(&place.name);
                    match binding {
                        None => {
                            self.error(statement.span, format!("unknown variable '{}'", place.name))
                        }
                        Some(binding) if !binding.mutable => self.error(
                            statement.span,
                            format!(
                                "cannot assign to immutable '{}'; declare with change",
                                place.name
                            ),
                        ),
                        _ => {}
                    }
                    if let Some(binding) = binding.filter(|binding| binding.typ == Type::Buffer) {
                        if !place.projections.is_empty() {
                            self.available(binding.slot, statement.span);
                            if let [Projection::Index(index)] = &place.projections[..] {
                                let index = self.expr(index);
                                if let Some(index) = &index {
                                    self.require(index, Type::Num, "buffer index");
                                }
                                self.available(binding.slot, statement.span);
                                let value = self.expr(value);
                                self.available(binding.slot, statement.span);
                                if let Some(value) = &value {
                                    self.require(value, Type::Num, "assignment target");
                                }
                                if let (Some(index), Some(value)) = (index, value) {
                                    output.push(IrStmt::BufferStore {
                                        slot: binding.slot,
                                        index,
                                        value,
                                    });
                                }
                            } else {
                                self.error(
                                    statement.span,
                                    "buffer assignment requires exactly one numeric index",
                                );
                                self.expr(value);
                            }
                            continue;
                        }
                    }
                    let target = self.place(place, binding.map(|b| b.typ), statement.span);
                    let value = self.expr(value);
                    if let (Some(binding), Some((typ, projections)), Some(value)) =
                        (binding, target, value)
                    {
                        self.require(&value, typ, "assignment target");
                        if projections.is_empty() {
                            if binding.typ == Type::Buffer {
                                self.owner_moves[binding.slot] = None;
                            }
                            output.push(IrStmt::Store(binding.slot, value));
                        } else {
                            output.push(IrStmt::StorePlace {
                                place: IrPlace {
                                    slot: binding.slot,
                                    projections,
                                },
                                value,
                            });
                        }
                    }
                }
                StmtKind::Say(expr) => {
                    if let Some(value) = self.expr(expr) {
                        if value.typ.scalar().is_none() {
                            self.error(
                                value.span,
                                "say expects a scalar; print aggregate fields or elements individually",
                            );
                        }
                        output.push(IrStmt::Say(value));
                    }
                }
                StmtKind::Return(expr) => {
                    if let Some(value) = self.expr(expr) {
                        self.require(&value, self.returns, "return value");
                        output.push(IrStmt::Return(value));
                    }
                    returns = true;
                }
                StmtKind::If { condition, yes, no } => {
                    let condition = self.expr(condition);
                    if let Some(condition) = &condition {
                        self.require(condition, Type::Flag, "when condition");
                    }
                    let incoming = self.owner_moves.clone();
                    let (yes, yes_returns) = self.block(yes, true);
                    let yes_state = self.owner_moves.clone();
                    self.restore_owners(&incoming);
                    let (no, no_returns) = self.block(no, true);
                    let no_state = self.owner_moves.clone();
                    match (yes_returns, no_returns) {
                        (false, false) => self
                            .join_owners(&yes_state[..incoming.len()], &no_state[..incoming.len()]),
                        (false, true) => self.restore_owners(&yes_state[..incoming.len()]),
                        (true, false) => self.restore_owners(&no_state[..incoming.len()]),
                        (true, true) => self.restore_owners(&incoming),
                    }
                    if let Some(condition) = condition {
                        output.push(IrStmt::If { condition, yes, no });
                    }
                    returns |= yes_returns && no_returns;
                }
                StmtKind::While { condition, body } => {
                    let incoming = self.owner_moves.clone();
                    let condition = self.expr(condition);
                    if let Some(condition) = &condition {
                        self.require(condition, Type::Flag, "repeat condition");
                    }
                    for (slot, before) in incoming.iter().enumerate() {
                        if self.locals[slot] == Type::Buffer
                            && before.is_none()
                            && self.owner_moves[slot].is_some()
                        {
                            let name = &self.declarations[slot].0;
                            self.owner_error(slot, statement.span, format!("repeat condition cannot move outer buffer '{name}'; inspect it or pass buffer_copy({name})"));
                        }
                    }
                    let after_condition = self.owner_moves.clone();
                    let (body, body_returns) = self.block(body, true);
                    if !body_returns {
                        for (slot, before) in after_condition.iter().enumerate() {
                            if self.locals[slot] == Type::Buffer
                                && before.is_none()
                                && self.owner_moves[slot].is_some()
                            {
                                let name = &self.declarations[slot].0;
                                self.owner_error(slot, statement.span, format!("repeat body moves outer buffer '{name}' without restoring it before the next iteration"));
                            }
                        }
                    }
                    // Zero body iterations are possible. A value unavailable
                    // before the loop cannot become definitely available after.
                    if body_returns {
                        self.restore_owners(&after_condition);
                    } else {
                        let after_body = self.owner_moves.clone();
                        self.join_owners(&after_condition, &after_body[..after_condition.len()]);
                    }
                    if let Some(condition) = condition {
                        output.push(IrStmt::While { condition, body });
                    }
                    // A loop might not execute; deliberately conservative even
                    // when its source condition happens to be `true`.
                }
            }
        }
        if !returns {
            let mut drops: Vec<_> = self
                .scopes
                .last()
                .into_iter()
                .flat_map(|scope| scope.values())
                .filter(|binding| binding.typ == Type::Buffer)
                .map(|binding| binding.slot)
                .collect();
            drops.sort_unstable_by(|a, b| b.cmp(a));
            for slot in drops {
                output.push(IrStmt::Drop(slot));
                self.owner_moves[slot] =
                    Some(statements.last().map(|s| s.span).unwrap_or_default());
            }
        }
        if nested {
            self.scopes.pop();
        }
        (output, returns)
    }

    fn place(
        &mut self,
        place: &Place,
        mut typ: Option<Type>,
        span: Span,
    ) -> Option<(Type, Vec<IrProjection>)> {
        let mut projections = Vec::new();
        for projection in &place.projections {
            match projection {
                Projection::Field { name, span } => {
                    if let Some(base) = typ {
                        if let Type::Record { id, .. } = base {
                            match self.records[id]
                                .fields
                                .iter()
                                .position(|field| field.name == *name)
                            {
                                Some(field) => {
                                    typ = Some(self.records[id].fields[field].typ);
                                    projections.push(IrProjection::Field(field));
                                }
                                None => {
                                    self.error(
                                        *span,
                                        format!(
                                            "record '{}' has no field '{name}'",
                                            self.records[id].name
                                        ),
                                    );
                                    typ = None;
                                }
                            }
                        } else {
                            self.error(
                                *span,
                                format!(
                                    "field access requires a record, got {}",
                                    type_name(base, self.records)
                                ),
                            );
                            typ = None;
                        }
                    }
                }
                Projection::Index(index) => {
                    let value = self.expr(index);
                    if let Some(value) = &value {
                        self.require(value, Type::Num, "array index");
                    }
                    if let Some(base) = typ {
                        if let Type::Array(element, _) = base {
                            typ = Some(element.typ());
                            if let Some(value) = value {
                                projections.push(IrProjection::Index(value));
                            } else {
                                typ = None;
                            }
                        } else {
                            self.error(
                                span,
                                format!(
                                    "indexed assignment requires an array, got {}",
                                    type_name(base, self.records)
                                ),
                            );
                            typ = None;
                        }
                    }
                }
            }
        }
        typ.map(|typ| (typ, projections))
    }

    fn expr(&mut self, expr: &Expr) -> Option<IrExpr> {
        let (kind, typ) = match &expr.kind {
            ExprKind::Literal(value) => (
                IrExprKind::Literal(value.clone()),
                match value {
                    Literal::Num(_) => Type::Num,
                    Literal::Flag(_) => Type::Flag,
                    Literal::Text(_) => Type::Text,
                },
            ),
            ExprKind::Var(name) => match self.binding(name) {
                Some(binding) => {
                    if binding.typ == Type::Buffer {
                        self.available(binding.slot, expr.span);
                        if self.owner_moves[binding.slot].is_none() {
                            self.owner_moves[binding.slot] = Some(expr.span);
                        }
                    }
                    (IrExprKind::Local(binding.slot), binding.typ)
                }
                None => {
                    self.error(expr.span, format!("unknown variable '{}'", name));
                    return None;
                }
            },
            ExprKind::Unary(operator, operand) => {
                let operand = self.expr(operand)?;
                let wanted = match operator {
                    Unary::Neg => Type::Num,
                    Unary::Not => Type::Flag,
                };
                self.require(&operand, wanted, "unary operator");
                (IrExprKind::Unary(*operator, Box::new(operand)), wanted)
            }
            ExprKind::Binary(operator, left, right) => {
                // Check both sides even when the first has an unresolved name.
                let left = self.expr(left);
                let after_left = self.owner_moves.clone();
                let right = self.expr(right);
                if matches!(operator, Binary::And | Binary::Or) {
                    let after_right = self.owner_moves.clone();
                    self.join_owners(&after_left, &after_right);
                }
                let (left, right) = (left?, right?);
                let typ = match operator {
                    Binary::And | Binary::Or => {
                        self.require(&left, Type::Flag, "boolean operator");
                        self.require(&right, Type::Flag, "boolean operator");
                        Type::Flag
                    }
                    Binary::Eq | Binary::Ne => {
                        if left.typ != right.typ || !matches!(left.typ, Type::Num | Type::Flag) {
                            self.error(expr.span, "equality requires matching num or flag operands; text equality and array equality are not supported");
                        }
                        Type::Flag
                    }
                    Binary::Add | Binary::Sub | Binary::Mul | Binary::Div | Binary::Rem => {
                        self.require(&left, Type::Num, "arithmetic operator");
                        self.require(&right, Type::Num, "arithmetic operator");
                        Type::Num
                    }
                    Binary::Lt | Binary::Le | Binary::Gt | Binary::Ge => {
                        self.require(&left, Type::Num, "comparison operator");
                        self.require(&right, Type::Num, "comparison operator");
                        Type::Flag
                    }
                };
                (
                    IrExprKind::Binary(*operator, Box::new(left), Box::new(right)),
                    typ,
                )
            }
            ExprKind::Call(name, arguments) => {
                let signature = self.signatures.get(name).cloned();
                let arguments: Vec<_> = arguments
                    .iter()
                    .map(|argument| self.expr(argument))
                    .collect();
                let Some(signature) = signature else {
                    self.error(expr.span, format!("unknown function '{}'", name));
                    return None;
                };
                if arguments.len() != signature.params.len() {
                    self.error(
                        expr.span,
                        format!(
                            "function '{}' expects {} arguments, got {}",
                            name,
                            signature.params.len(),
                            arguments.len()
                        ),
                    );
                }
                for (index, (argument, wanted)) in
                    arguments.iter().zip(&signature.params).enumerate()
                {
                    if let Some(argument) = argument {
                        self.require(
                            argument,
                            *wanted,
                            &format!("argument {} of '{}'", index + 1, name),
                        );
                    }
                }
                let arguments: Option<Vec<_>> = arguments.into_iter().collect();
                (
                    IrExprKind::Call(signature.index, arguments?),
                    signature.returns,
                )
            }
            ExprKind::Record { name, fields } => {
                let values: Vec<_> = fields.iter().map(|field| self.expr(&field.value)).collect();
                let Some(&id) = self.record_ids.get(name) else {
                    self.error(expr.span, format!("unknown record type '{name}'"));
                    return None;
                };
                let mut seen = vec![false; self.records[id].fields.len()];
                let mut output = Vec::new();
                for (field, value) in fields.iter().zip(values) {
                    let Some(index) = self.records[id]
                        .fields
                        .iter()
                        .position(|item| item.name == field.name)
                    else {
                        self.error(
                            field.span,
                            format!("record '{name}' has no field '{}'", field.name),
                        );
                        continue;
                    };
                    if seen[index] {
                        self.error(
                            field.span,
                            format!("duplicate initializer for field '{}'", field.name),
                        );
                    }
                    seen[index] = true;
                    if let Some(value) = value {
                        self.require(
                            &value,
                            self.records[id].fields[index].typ,
                            &format!("field '{}' of '{name}'", field.name),
                        );
                        output.push((index, value));
                    }
                }
                for (index, initialized) in seen.iter().enumerate() {
                    if !initialized {
                        self.error(
                            expr.span,
                            format!(
                                "missing field '{}' in record '{name}'",
                                self.records[id].fields[index].name
                            ),
                        );
                    }
                }
                (
                    IrExprKind::Record {
                        record: id,
                        fields: output,
                    },
                    Type::Record {
                        id,
                        words: self.records[id].words,
                    },
                )
            }
            ExprKind::Field { base, name } => {
                let base = self.expr(base)?;
                let Type::Record { id, .. } = base.typ else {
                    self.error(
                        expr.span,
                        format!(
                            "field access requires a record, got {}",
                            type_name(base.typ, self.records)
                        ),
                    );
                    return None;
                };
                let Some(field) = self.records[id]
                    .fields
                    .iter()
                    .position(|item| item.name == *name)
                else {
                    self.error(
                        expr.span,
                        format!("record '{}' has no field '{name}'", self.records[id].name),
                    );
                    return None;
                };
                let typ = self.records[id].fields[field].typ;
                (
                    IrExprKind::Field {
                        base: Box::new(base),
                        field,
                    },
                    typ,
                )
            }
            ExprKind::Array(elements) => {
                let values: Vec<_> = elements.iter().map(|element| self.expr(element)).collect();
                if elements.is_empty() {
                    self.error(expr.span, "empty array literals are not supported; an array requires at least one scalar element");
                    return None;
                }
                if elements.len() > MAX_ARRAY_LEN {
                    self.error(
                        expr.span,
                        format!("array length must be between 1 and {MAX_ARRAY_LEN}"),
                    );
                    return None;
                }
                let values: Option<Vec<_>> = values.into_iter().collect();
                let values = values?;
                let first = values[0].typ;
                let Some(element) = first.scalar() else {
                    self.error(
                        expr.span,
                        "array elements must be scalar; nested arrays are not supported",
                    );
                    return None;
                };
                for value in &values {
                    self.require(value, first, "array literal element");
                }
                let typ = Type::Array(element, values.len());
                (IrExprKind::Array(values), typ)
            }
            ExprKind::ArrayRepeat(value, length) => {
                let value = self.expr(value)?;
                if !(1..=MAX_ARRAY_LEN).contains(length) {
                    self.error(
                        expr.span,
                        format!("array length must be between 1 and {MAX_ARRAY_LEN}"),
                    );
                    return None;
                }
                let Some(element) = value.typ.scalar() else {
                    self.error(
                        expr.span,
                        "array elements must be scalar; nested arrays are not supported",
                    );
                    return None;
                };
                (
                    IrExprKind::ArrayRepeat(Box::new(value), *length),
                    Type::Array(element, *length),
                )
            }
            ExprKind::Buffer(length) => {
                let length = self.expr(length)?;
                self.require(&length, Type::Num, "buffer length");
                (IrExprKind::Buffer(Box::new(length)), Type::Buffer)
            }
            ExprKind::BufferCopy(value) => {
                let slot = self.buffer_local(value, "buffer_copy")?;
                (IrExprKind::BufferCopy { slot }, Type::Buffer)
            }
            ExprKind::Index(array, index) => {
                if let ExprKind::Var(name) = &array.kind {
                    if let Some(binding) = self
                        .binding(name)
                        .filter(|binding| binding.typ == Type::Buffer)
                    {
                        self.available(binding.slot, array.span);
                        let index = self.expr(index)?;
                        self.require(&index, Type::Num, "buffer index");
                        self.available(binding.slot, expr.span);
                        return Some(IrExpr {
                            kind: IrExprKind::BufferGet {
                                slot: binding.slot,
                                index: Box::new(index),
                            },
                            typ: Type::Num,
                            span: expr.span,
                        });
                    }
                }
                let array = self.expr(array);
                let index = self.expr(index);
                if let Some(index) = &index {
                    self.require(index, Type::Num, "array index");
                }
                let (array, index) = (array?, index?);
                if array.typ == Type::Buffer {
                    self.error(
                        expr.span,
                        "buffer indexing requires a named buffer local; bind the value first",
                    );
                    return None;
                }
                let Type::Array(element, _) = array.typ else {
                    self.error(
                        expr.span,
                        format!("indexing requires an array, got {}", array.typ),
                    );
                    return None;
                };
                (
                    IrExprKind::Index(Box::new(array), Box::new(index)),
                    element.typ(),
                )
            }
            ExprKind::Len(array) => {
                if let ExprKind::Var(name) = &array.kind {
                    if let Some(binding) = self
                        .binding(name)
                        .filter(|binding| binding.typ == Type::Buffer)
                    {
                        self.available(binding.slot, array.span);
                        return Some(IrExpr {
                            kind: IrExprKind::BufferLen { slot: binding.slot },
                            typ: Type::Num,
                            span: expr.span,
                        });
                    }
                }
                let array = self.expr(array)?;
                if array.typ == Type::Buffer {
                    self.error(
                        expr.span,
                        "len on a buffer requires a named buffer local; bind the value first",
                    );
                    return None;
                }
                if !matches!(array.typ, Type::Array(..)) {
                    self.error(
                        expr.span,
                        format!("len expects an array, got {}", array.typ),
                    );
                }
                (IrExprKind::Len(Box::new(array)), Type::Num)
            }
        };
        Some(IrExpr {
            kind,
            typ,
            span: expr.span,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compile(source: &str) -> Result<IrProgram, Vec<Diagnostic>> {
        check(crate::parser::parse(source).expect("test source must parse"))
    }

    fn rejected(source: &str, expected: &str) {
        let errors = compile(source).expect_err("source must fail semantic checks");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "expected {expected:?}, got {errors:?}"
        );
    }

    #[test]
    fn resolves_forward_calls_and_recursion() {
        let program = compile("craft main() -> num:\n    give count(2)\ncraft count(n: num) -> num:\n    when n == 0:\n        give 0\n    otherwise:\n        give count(n - 1)\n").unwrap();
        assert_eq!(program.main, 0);
        assert!(matches!(
            &program.functions[0].body[0],
            IrStmt::Return(IrExpr {
                kind: IrExprKind::Call(1, _),
                ..
            })
        ));
    }

    #[test]
    fn checks_immutability_and_assignment_type() {
        rejected(
            "craft main() -> num:\n    keep x = 1\n    x = 2\n    give 0\n",
            "immutable",
        );
        rejected(
            "craft main() -> num:\n    change x = 1\n    x = true\n    give 0\n",
            "expects num",
        );
        rejected(
            "craft f(x: num) -> num:\n    x = 1\n    give x\ncraft main() -> num:\n    give f(0)\n",
            "immutable",
        );
    }

    #[test]
    fn requires_returns_on_both_paths() {
        rejected(
            "craft main() -> num:\n    when true:\n        give 0\n",
            "every path",
        );
        rejected(
            "craft main() -> num:\n    repeat true:\n        give 0\n",
            "every path",
        );
        compile("craft main() -> num:\n    when true:\n        give 0\n    otherwise:\n        give 1\n").unwrap();
    }

    #[test]
    fn diagnoses_unreachable_statements() {
        rejected(
            "craft main() -> num:\n    give 0\n    say 1\n",
            "unreachable",
        );
        rejected("craft main() -> num:\n    when true:\n        give 0\n    otherwise:\n        give 1\n    say 2\n", "unreachable");
    }

    #[test]
    fn block_names_do_not_escape_and_slots_are_distinct() {
        rejected(
            "craft main() -> num:\n    when true:\n        keep x = 1\n    say x\n    give 0\n",
            "unknown variable",
        );
        let program = compile("craft main() -> num:\n    keep x = 1\n    when true:\n        keep x = 2\n        say x\n    say x\n    give 0\n").unwrap();
        assert_eq!(program.functions[0].locals, vec![Type::Num, Type::Num]);
    }

    #[test]
    fn rejects_duplicates() {
        rejected(
            "craft main() -> num:\n    give 0\ncraft main() -> num:\n    give 0\n",
            "duplicate function",
        );
        rejected(
            "craft main() -> num:\n    keep x = 1\n    keep x = 2\n    give 0\n",
            "already declared",
        );
    }

    #[test]
    fn rejects_duplicate_and_excessive_parameters() {
        // Build this AST directly because a parser may also diagnose duplicate
        // parameters. The semantic boundary must enforce its own invariants.
        let span = Span { line: 1, column: 1 };
        let function = Function {
            name: "main".to_owned(),
            params: (0..7)
                .map(|_| Param {
                    name: "x".to_owned(),
                    typ: Type::Num.into(),
                    span,
                })
                .collect(),
            returns: Type::Num.into(),
            body: vec![Stmt {
                kind: StmtKind::Return(Expr {
                    kind: ExprKind::Literal(Literal::Num(0)),
                    span,
                }),
                span,
            }],
            span,
        };
        let errors = check(Program {
            functions: vec![function],
            records: vec![],
        })
        .unwrap_err();
        assert!(errors
            .iter()
            .any(|error| error.message.contains("six parameters")));
        assert_eq!(
            errors
                .iter()
                .filter(|error| error.message.contains("already declared"))
                .count(),
            6
        );
    }

    #[test]
    fn checks_main_signature() {
        rejected("craft f() -> num:\n    give 0\n", "entry point");
        rejected("craft main(x: num) -> num:\n    give x\n", "entry point");
        rejected("craft main() -> flag:\n    give true\n", "entry point");
    }

    #[test]
    fn validates_operator_types_and_calls() {
        rejected(
            "craft main() -> num:\n    say 1 + true\n    give 0\n",
            "expects num",
        );
        rejected(
            "craft main() -> num:\n    say 1 and true\n    give 0\n",
            "expects flag",
        );
        rejected(
            "craft main() -> num:\n    say \"x\" == \"x\"\n    give 0\n",
            "text equality",
        );
        rejected(
            "craft main() -> num:\n    say nope()\n    give 0\n",
            "unknown function",
        );
        rejected(
            "craft f(n: num) -> num:\n    give n\ncraft main() -> num:\n    give f(true)\n",
            "argument 1",
        );
        rejected(
            "craft f(n: num) -> num:\n    give n\ncraft main() -> num:\n    give f()\n",
            "expects 1 arguments",
        );
    }

    #[test]
    fn collects_independent_errors() {
        let errors = compile("craft main() -> num:\n    say missing_left + missing_right\n    when 1:\n        say 2\n    give true\n").unwrap_err();
        assert_eq!(errors.len(), 4, "{errors:?}");
    }

    #[test]
    fn arrays_support_value_types_parameters_returns_and_mutation() {
        let ir = compile("craft copy(items: [num; 3]) -> [num; 3]:\n    change result = items\n    result[0] = result[1]\n    give result\ncraft main() -> num:\n    change numbers = [1, 2, 3]\n    keep other = copy(numbers)\n    numbers = [4, 5, 6]\n    say other[0]\n    say len(numbers)\n    keep flags = [true, false]\n    say flags[1]\n    keep names = [\"one\", \"two\"]\n    say names[0]\n    give 0\n").unwrap();
        assert_eq!(
            ir.functions[0].params,
            vec![Type::Array(ScalarType::Num, 3)]
        );
        assert_eq!(ir.functions[0].returns, Type::Array(ScalarType::Num, 3));
        crate::ir::verify(&ir).unwrap();
    }

    #[test]
    fn array_literals_require_nonempty_homogeneous_scalar_elements() {
        rejected(
            "craft main() -> num:\n    keep values = []\n    give 0\n",
            "empty array",
        );
        rejected(
            "craft main() -> num:\n    keep values = [1, true]\n    give 0\n",
            "array literal element expects num",
        );
        rejected(
            "craft main() -> num:\n    keep values = [[1], [2]]\n    give 0\n",
            "nested arrays",
        );
        rejected(
            "craft main() -> num:\n    keep values = [[1]; 2]\n    give 0\n",
            "nested arrays",
        );
    }

    #[test]
    fn array_copy_and_call_types_include_length_and_element() {
        rejected(
            "craft main() -> num:\n    change values = [1, 2]\n    values = [3]\n    give 0\n",
            "expects [num; 2]",
        );
        rejected("craft use_values(values: [num; 2]) -> num:\n    give values[0]\ncraft main() -> num:\n    give use_values([1])\n", "argument 1");
        rejected("craft result() -> [num; 2]:\n    give [true, false]\ncraft main() -> num:\n    give 0\n", "return value expects [num; 2]");
    }

    #[test]
    fn indexed_mutation_requires_mutable_array_and_exact_element_type() {
        rejected(
            "craft main() -> num:\n    keep values = [1]\n    values[0] = 2\n    give 0\n",
            "cannot assign to immutable 'values'; declare with change",
        );
        rejected("craft use_values(values: [num; 1]) -> num:\n    values[0] = 2\n    give 0\ncraft main() -> num:\n    give 0\n", "cannot assign to immutable 'values'; declare with change");
        rejected(
            "craft main() -> num:\n    change values = [1]\n    values[0] = false\n    give 0\n",
            "assignment target expects num, got flag",
        );
        rejected(
            "craft main() -> num:\n    change value = 1\n    value[0] = 2\n    give 0\n",
            "requires an array",
        );
    }

    #[test]
    fn array_index_length_print_and_comparison_contracts() {
        for (body, message) in [
            ("    say [1][true]\n", "array index expects num"),
            ("    say 1[0]\n", "indexing requires an array"),
            ("    say len(1)\n", "len expects an array"),
            ("    say [1]\n", "say expects a scalar"),
            ("    say [1] == [1]\n", "array equality"),
            ("    say [1] + [2]\n", "arithmetic operator expects num"),
            (
                "    change values = [1]\n    values[true] = 2\n",
                "array index expects num",
            ),
        ] {
            rejected(
                &format!("craft main() -> num:\n{body}    give 0\n"),
                message,
            );
        }
        // Bounds faults, including obvious constants, have one runtime contract
        // independent of optimization. The type checker must accept these.
        compile("craft main() -> num:\n    change values = [1]\n    values[-1] = 2\n    say values[9223372036854775807]\n    give 0\n").unwrap();
    }

    #[test]
    fn repeated_arrays_and_frame_resource_limits_are_checked() {
        let ir = compile(
            "craft main() -> num:\n    keep values = [7; 4096]\n    say len(values)\n    give 0\n",
        )
        .unwrap();
        assert_eq!(
            ir.functions[0].locals,
            vec![Type::Array(ScalarType::Num, MAX_ARRAY_LEN)]
        );
        let function = |count| {
            format!("craft large(values: [num; 4096]) -> num:\n{}    give 0\ncraft main() -> num:\n    give 0\n", "    say len(values)\n".repeat(count))
        };
        compile(&function(14)).unwrap();
        compile(&function(1000)).unwrap();
        let locals = format!(
            "craft main() -> num:\n{}    give 0\n",
            (0..17)
                .map(|i| format!("    keep values{i} = [0; 4096]\n"))
                .collect::<String>()
        );
        rejected(&locals, "fixed local storage exceeds compiler limit");
    }

    #[test]
    fn records_resolve_forward_layouts_and_preserve_initializer_source_order() {
        let ir = compile("record Outer:\n    nested: Inner\n    items: [num; 2]\nrecord Inner:\n    label: text\n    valid: flag\ncraft main() -> num:\n    change p = Outer { items: [1, 2], nested: Inner { valid: true, label: \"ok\" } }\n    p.nested.label = \"changed\"\n    p.items[1] = 9\n    keep copied = p.nested\n    say copied.label\n    give 0\n").unwrap();
        assert_eq!(ir.records[0].words, 4);
        assert_eq!(ir.records[0].fields[1].offset, 2);
        assert_eq!(
            ir.records[0].fields[0].typ,
            Type::Record { id: 1, words: 2 }
        );
        let IrStmt::Store(_, value) = &ir.functions[0].body[0] else {
            panic!()
        };
        let IrExprKind::Record { fields, .. } = &value.kind else {
            panic!()
        };
        assert_eq!(
            fields.iter().map(|(field, _)| *field).collect::<Vec<_>>(),
            vec![1, 0]
        );
        crate::ir::verify(&ir).unwrap();
    }

    #[test]
    fn records_are_nominal_with_readable_type_mismatch_diagnostics() {
        rejected("record Point:\n    x: num\nrecord Other:\n    x: num\ncraft take(p: Point) -> num:\n    give p.x\ncraft main() -> num:\n    give take(Other { x: 1 })\n", "expects Point, got Other");
        rejected("record Point:\n    x: num\nrecord Other:\n    x: num\ncraft make() -> Point:\n    give Other { x: 1 }\ncraft main() -> num:\n    give 0\n", "expects Point, got Other");
    }

    #[test]
    fn records_reject_invalid_declarations_and_layout_cycles() {
        for (declarations, message) in [
            (
                "record A:\n    x: Missing\n",
                "unknown record type 'Missing'",
            ),
            ("record A:\n    x: A\n", "A -> A"),
            ("record A:\n    x: B\nrecord B:\n    y: A\n", "A -> B -> A"),
            ("record A:\n    x: num\n    x: flag\n", "duplicate field"),
            (
                "record A:\n    x: num\nrecord A:\n    y: num\n",
                "duplicate record",
            ),
        ] {
            rejected(
                &format!("{declarations}craft main() -> num:\n    give 0\n"),
                message,
            );
        }
        rejected("record same:\n    x: num\ncraft same() -> num:\n    give 1\ncraft main() -> num:\n    give 0\n", "conflicts with a record declaration");
    }

    #[test]
    fn records_require_exact_constructor_fields_and_mutation_types() {
        for (body, message) in [
            ("    keep p = Point { x: 1 }\n", "missing field 'y'"),
            (
                "    keep p = Point { x: 1, y: 2, z: 3 }\n",
                "has no field 'z'",
            ),
            (
                "    keep p = Point { x: 1, y: 2, x: 3 }\n",
                "duplicate initializer",
            ),
            (
                "    keep p = Point { x: true, y: 2 }\n",
                "expects num, got flag",
            ),
            (
                "    change p = Point { x: 1, y: 2 }\n    p.z = 3\n",
                "has no field 'z'",
            ),
            (
                "    keep p = Point { x: 1, y: 2 }\n    p.x = 3\n",
                "immutable",
            ),
            (
                "    change p = Point { x: 1, y: 2 }\n    p.x = true\n",
                "expects num, got flag",
            ),
            (
                "    keep p = Point { x: 1, y: 2 }\n    say p\n",
                "say expects a scalar",
            ),
            (
                "    keep p = Point { x: 1, y: 2 }\n    say p == p\n",
                "equality requires",
            ),
            (
                "    keep p = Point { x: 1, y: 2 }\n    say p[0]\n",
                "indexing requires an array",
            ),
        ] {
            rejected(&format!("record Point:\n    x: num\n    y: num\ncraft main() -> num:\n{body}    give 0\n"), message);
        }
        rejected("record Point:\n    x: num\ncraft edit(p: Point) -> Point:\n    p.x = 4\n    give p\ncraft main() -> num:\n    give 0\n", "immutable");
    }

    #[test]
    fn record_layout_depth_and_width_are_checked_even_after_cached_children() {
        let chain = |count: usize| {
            let mut source = String::new();
            for id in (0..count).rev() {
                source.push_str(&format!(
                    "record R{id}:\n    value: {}\n",
                    if id + 1 == count {
                        "num".into()
                    } else {
                        format!("R{}", id + 1)
                    }
                ));
            }
            source.push_str("craft main() -> num:\n    give 0\n");
            source
        };
        compile(&chain(MAX_RECORD_DEPTH)).unwrap();
        rejected(&chain(MAX_RECORD_DEPTH + 1), "record nesting exceeds");
        let mut source = String::from("record Huge:\n");
        for i in 0..5 {
            source.push_str(&format!("    value{i}: [num; 4096]\n"));
        }
        source.push_str("craft main() -> num:\n    give 0\n");
        rejected(&source, "record layout exceeds");
    }
}
