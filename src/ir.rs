//! Invariants at the boundary between semantic analysis, optimization and codegen.
//!
//! This verifier checks typed, structured IR and conservative definite
//! initialization. It is an internal compiler consistency check, not a proof of
//! memory safety or a sandbox for arbitrary compiler inputs.
use crate::model::*;

/// Conservative pre-CFG estimate: locals, a saved result pointer, and one buffer
/// per aggregate expression. It may exceed the native cap when lifetimes permit
/// reuse. Fixed locals are checked here; the CFG allocator checks the actual frame.
pub fn frame_words(function: &IrFunction) -> Result<usize, String> {
    fn add(total: &mut usize, words: usize) -> Result<(), String> {
        *total = total
            .checked_add(words)
            .ok_or("frame word count overflow")?;
        Ok(())
    }
    fn typ(typ: Type) -> Result<(), String> {
        match typ {
            Type::Array(_, length) if !(1..=MAX_ARRAY_LEN).contains(&length) => {
                return Err(format!(
                    "array length must be between 1 and {MAX_ARRAY_LEN}"
                ))
            }
            Type::Record { words, .. } if !(1..=MAX_RECORD_WORDS).contains(&words) => {
                return Err(format!(
                    "record width must be between 1 and {MAX_RECORD_WORDS}"
                ))
            }
            _ => {}
        }
        Ok(())
    }
    fn expression(expr: &IrExpr, total: &mut usize) -> Result<(), String> {
        typ(expr.typ)?;
        if expr.typ.aggregate() {
            add(total, expr.typ.words())?;
        }
        match &expr.kind {
            IrExprKind::Unary(_, value)
            | IrExprKind::Buffer(value)
            | IrExprKind::Len(value)
            | IrExprKind::ArrayRepeat(value, _)
            | IrExprKind::Field { base: value, .. } => expression(value, total)?,
            IrExprKind::Binary(_, left, right) | IrExprKind::Index(left, right) => {
                expression(left, total)?;
                expression(right, total)?;
            }
            IrExprKind::BufferGet { index, .. } => expression(index, total)?,
            IrExprKind::Record { fields, .. } => {
                for (_, value) in fields {
                    expression(value, total)?;
                }
            }
            IrExprKind::Call(_, args) | IrExprKind::Array(args) => {
                for arg in args {
                    expression(arg, total)?;
                }
            }
            _ => {}
        }
        Ok(())
    }
    fn block(statements: &[IrStmt], total: &mut usize) -> Result<(), String> {
        for statement in statements {
            match statement {
                IrStmt::Drop(_) => {}
                IrStmt::BufferStore { index, value, .. } => {
                    expression(index, total)?;
                    expression(value, total)?;
                }
                IrStmt::Store(_, value) | IrStmt::Say(value) | IrStmt::Return(value) => {
                    expression(value, total)?
                }
                IrStmt::StorePlace { place, value } => {
                    for projection in &place.projections {
                        if let IrProjection::Index(index) = projection {
                            expression(index, total)?;
                        }
                    }
                    expression(value, total)?;
                }
                IrStmt::If { condition, yes, no } => {
                    expression(condition, total)?;
                    block(yes, total)?;
                    block(no, total)?;
                }
                IrStmt::While { condition, body } => {
                    expression(condition, total)?;
                    block(body, total)?;
                }
            }
        }
        Ok(())
    }
    let result = (|| {
        typ(function.returns)?;
        for parameter in &function.params {
            typ(*parameter)?;
        }
        let mut words = 1;
        for local in &function.locals {
            typ(*local)?;
            add(&mut words, local.words())?;
        }
        let fixed = words - 1 + usize::from(function.returns.aggregate());
        if fixed > MAX_FRAME_WORDS {
            return Err(format!(
                "fixed local storage exceeds compiler limit of {MAX_FRAME_WORDS} words"
            ));
        }
        block(&function.body, &mut words)?;
        Ok(words)
    })();
    result.map_err(|message: String| format!("IR function '{}': {message}", function.name))
}

/// Validate a resolved type against the canonical record table.
pub(crate) fn canonical_type(typ: Type, records: &[IrRecord]) -> Result<(), String> {
    match typ {
        Type::Array(_, length) if !(1..=MAX_ARRAY_LEN).contains(&length) => Err(format!(
            "array length must be between 1 and {MAX_ARRAY_LEN}"
        )),
        Type::Record { id, words } => {
            let record = records
                .get(id)
                .ok_or_else(|| format!("record id {id} is out of bounds"))?;
            if words != record.words {
                return Err(format!(
                    "cached record width {words} does not match record '{}' width {}",
                    record.name, record.words
                ));
            }
            if !(1..=MAX_RECORD_WORDS).contains(&words) {
                return Err(format!(
                    "record width must be between 1 and {MAX_RECORD_WORDS}"
                ));
            }
            Ok(())
        }
        _ => Ok(()),
    }
}
pub(crate) fn verify_records(records: &[IrRecord]) -> Result<(), String> {
    if records.len() > MAX_RECORD_TYPES {
        return Err(format!(
            "record count exceeds compiler limit of {MAX_RECORD_TYPES}"
        ));
    }
    let mut names = std::collections::HashSet::new();
    for record in records {
        if !names.insert(&record.name) {
            return Err(format!("duplicate record '{}'", record.name));
        }
        if !(1..=MAX_RECORD_FIELDS).contains(&record.fields.len()) {
            return Err(format!(
                "record '{}' requires 1..={MAX_RECORD_FIELDS} fields",
                record.name
            ));
        }
        if !(1..=MAX_RECORD_WORDS).contains(&record.words) {
            return Err(format!(
                "record '{}' width must be between 1 and {MAX_RECORD_WORDS}",
                record.name
            ));
        }
        let mut names = std::collections::HashSet::new();
        let mut words = 0usize;
        for field in &record.fields {
            if field.typ == Type::Buffer {
                return Err(format!(
                    "record '{}' cannot contain an owned buffer",
                    record.name
                ));
            }
            canonical_type(field.typ, records)?;
            if !names.insert(&field.name) {
                return Err(format!(
                    "duplicate field '{}' in record '{}'",
                    field.name, record.name
                ));
            }
            if field.offset != words {
                return Err(format!(
                    "record '{}' field '{}' offset is not contiguous",
                    record.name, field.name
                ));
            }
            words = words
                .checked_add(field.typ.words())
                .ok_or("record layout width overflow")?;
            if words > MAX_RECORD_WORDS {
                return Err(format!("record '{}' exceeds layout limit", record.name));
            }
        }
        if words != record.words {
            return Err(format!(
                "record '{}' layout width does not match its fields",
                record.name
            ));
        }
    }
    fn visit(
        id: usize,
        records: &[IrRecord],
        states: &mut [u8],
        heights: &mut [usize],
        depth: usize,
    ) -> Result<usize, String> {
        if states[id] == 1 {
            return Err(format!("record layout cycle at '{}'", records[id].name));
        }
        if states[id] == 2 {
            return Ok(heights[id]);
        }
        if depth >= MAX_RECORD_DEPTH {
            return Err(format!(
                "record nesting exceeds compiler limit of {MAX_RECORD_DEPTH}"
            ));
        }
        states[id] = 1;
        let mut height = 1usize;
        for field in &records[id].fields {
            if let Type::Record { id: child, .. } = field.typ {
                height = height.max(visit(child, records, states, heights, depth + 1)? + 1);
            }
        }
        if height > MAX_RECORD_DEPTH {
            return Err(format!(
                "record nesting exceeds compiler limit of {MAX_RECORD_DEPTH}"
            ));
        }
        states[id] = 2;
        heights[id] = height;
        Ok(height)
    }
    let mut states = vec![0; records.len()];
    let mut heights = vec![0; records.len()];
    for id in 0..records.len() {
        visit(id, records, &mut states, &mut heights, 0)?;
    }
    Ok(())
}

/// Verify the contracts required by every native backend.
pub fn verify(program: &IrProgram) -> Result<(), String> {
    verify_records(&program.records)?;
    let main = program.functions.get(program.main).ok_or_else(|| {
        format!(
            "IR entry: main function index {} is out of bounds for {} functions",
            program.main,
            program.functions.len()
        )
    })?;
    if !main.params.is_empty() || main.returns != Type::Num {
        return Err(format!(
            "IR function '{}': entry signature must have no parameters and return num",
            main.name
        ));
    }

    for function in &program.functions {
        let checker = Verifier { program, function };
        for typ in function
            .params
            .iter()
            .chain(&function.locals)
            .chain(std::iter::once(&function.returns))
        {
            canonical_type(*typ, &program.records).map_err(|e| checker.error(e))?;
        }
        frame_words(function)?;
        if function.params.len() > 6 {
            return Err(checker.error("function has more than six parameters"));
        }
        if !function.locals.starts_with(&function.params) {
            return Err(checker.error("parameter types must match the prefix of local slots"));
        }
        let mut initialized = vec![false; function.locals.len()];
        initialized[..function.params.len()].fill(true);
        if !checker.block(&function.body, &mut initialized)? {
            return Err(checker.error("function does not return on every path"));
        }
    }
    Ok(())
}

struct Verifier<'a> {
    program: &'a IrProgram,
    function: &'a IrFunction,
}

impl Verifier<'_> {
    fn error(&self, context: impl std::fmt::Display) -> String {
        format!("IR function '{}': {}", self.function.name, context)
    }

    fn require(&self, actual: Type, expected: Type, context: &str) -> Result<(), String> {
        if actual != expected {
            return Err(self.error(format!("{context} expects {expected}, got {actual}")));
        }
        Ok(())
    }

    fn local_type(&self, slot: usize) -> Result<Type, String> {
        self.function
            .locals
            .get(slot)
            .copied()
            .ok_or_else(|| self.error(format!("local slot {slot} is out of bounds")))
    }

    fn buffer_local(&self, slot: usize, initialized: &[bool]) -> Result<(), String> {
        self.require(self.local_type(slot)?, Type::Buffer, "buffer local")?;
        if !initialized[slot] {
            return Err(self.error(format!(
                "buffer local {slot} is not definitely available (moved or uninitialized)"
            )));
        }
        Ok(())
    }

    fn expr(&self, expression: &IrExpr, initialized: &mut [bool]) -> Result<Type, String> {
        canonical_type(expression.typ, &self.program.records).map_err(|e| self.error(e))?;
        let actual = match &expression.kind {
            IrExprKind::Literal(literal) => match literal {
                Literal::Num(_) => Type::Num,
                Literal::Flag(_) => Type::Flag,
                Literal::Text(value) => {
                    if value.contains('\0') {
                        return Err(self.error("text literal contains unsupported embedded NUL"));
                    }
                    Type::Text
                }
            },
            IrExprKind::Local(slot) => {
                let typ = self.local_type(*slot)?;
                if !initialized[*slot] {
                    return Err(
                        self.error(format!("local slot {slot} is not definitely initialized"))
                    );
                }
                if typ == Type::Buffer {
                    initialized[*slot] = false;
                }
                typ
            }
            IrExprKind::Buffer(length) => {
                let length = self.expr(length, initialized)?;
                self.require(length, Type::Num, "buffer length")?;
                Type::Buffer
            }
            IrExprKind::BufferCopy { slot } | IrExprKind::BufferLen { slot } => {
                self.buffer_local(*slot, initialized)?;
                if matches!(expression.kind, IrExprKind::BufferCopy { .. }) {
                    Type::Buffer
                } else {
                    Type::Num
                }
            }
            IrExprKind::BufferGet { slot, index } => {
                self.buffer_local(*slot, initialized)?;
                let index = self.expr(index, initialized)?;
                self.require(index, Type::Num, "buffer index")?;
                // Index evaluation may itself consume an owner via a call.
                self.buffer_local(*slot, initialized)?;
                Type::Num
            }
            IrExprKind::Unary(operator, operand) => {
                let actual = self.expr(operand, initialized)?;
                let expected = match operator {
                    Unary::Neg => Type::Num,
                    Unary::Not => Type::Flag,
                };
                self.require(actual, expected, "unary operand")?;
                expected
            }
            IrExprKind::Binary(operator, left, right) => {
                // Even a short-circuited RHS must contain valid typed IR. Source
                // checking likewise validates both operands before optimization.
                let left = self.expr(left, initialized)?;
                let skipped = initialized.to_vec();
                let right = self.expr(right, initialized)?;
                if matches!(operator, Binary::And | Binary::Or) {
                    for (state, before) in initialized.iter_mut().zip(skipped) {
                        *state &= before;
                    }
                }
                match operator {
                    Binary::And | Binary::Or => {
                        self.require(left, Type::Flag, "boolean left operand")?;
                        self.require(right, Type::Flag, "boolean right operand")?;
                        Type::Flag
                    }
                    Binary::Eq | Binary::Ne => {
                        if left != right || !matches!(left, Type::Num | Type::Flag) {
                            return Err(
                                self.error("equality requires matching num or flag operands")
                            );
                        }
                        Type::Flag
                    }
                    Binary::Add | Binary::Sub | Binary::Mul | Binary::Div | Binary::Rem => {
                        self.require(left, Type::Num, "arithmetic left operand")?;
                        self.require(right, Type::Num, "arithmetic right operand")?;
                        Type::Num
                    }
                    Binary::Lt | Binary::Le | Binary::Gt | Binary::Ge => {
                        self.require(left, Type::Num, "comparison left operand")?;
                        self.require(right, Type::Num, "comparison right operand")?;
                        Type::Flag
                    }
                }
            }
            IrExprKind::Call(index, arguments) => {
                let callee = self.program.functions.get(*index).ok_or_else(|| {
                    self.error(format!("call function index {index} is out of bounds"))
                })?;
                if arguments.len() != callee.params.len() {
                    return Err(self.error(format!(
                        "call '{}' expects {} arguments, got {}",
                        callee.name,
                        callee.params.len(),
                        arguments.len()
                    )));
                }
                for (index, (argument, expected)) in
                    arguments.iter().zip(&callee.params).enumerate()
                {
                    let actual = self.expr(argument, initialized)?;
                    self.require(
                        actual,
                        *expected,
                        &format!("call '{}' argument {}", callee.name, index + 1),
                    )?;
                }
                callee.returns
            }
            IrExprKind::Record { record, fields } => {
                let declaration =
                    self.program.records.get(*record).ok_or_else(|| {
                        self.error(format!("record id {record} is out of bounds"))
                    })?;
                let mut seen = vec![false; declaration.fields.len()];
                for (index, value) in fields {
                    let field = declaration.fields.get(*index).ok_or_else(|| {
                        self.error(format!("record field index {index} is out of bounds"))
                    })?;
                    if seen[*index] {
                        return Err(self.error("duplicate record field initializer"));
                    }
                    seen[*index] = true;
                    let actual = self.expr(value, initialized)?;
                    self.require(actual, field.typ, "record field initializer")?;
                }
                if seen.iter().any(|seen| !seen) {
                    return Err(self.error("missing record field initializer"));
                }
                Type::Record {
                    id: *record,
                    words: declaration.words,
                }
            }
            IrExprKind::Field { base, field } => {
                let base = self.expr(base, initialized)?;
                let Type::Record { id, .. } = base else {
                    return Err(self.error("field access requires a record"));
                };
                self.program.records[id]
                    .fields
                    .get(*field)
                    .ok_or_else(|| {
                        self.error(format!("record field index {field} is out of bounds"))
                    })?
                    .typ
            }
            IrExprKind::Array(elements) => {
                if !(1..=MAX_ARRAY_LEN).contains(&elements.len()) {
                    return Err(self.error(format!(
                        "array literal requires 1..={MAX_ARRAY_LEN} elements"
                    )));
                }
                let first = self.expr(&elements[0], initialized)?;
                let element = first
                    .scalar()
                    .ok_or_else(|| self.error("array elements must be scalar"))?;
                for value in &elements[1..] {
                    let actual = self.expr(value, initialized)?;
                    self.require(actual, first, "array literal element")?;
                }
                Type::Array(element, elements.len())
            }
            IrExprKind::ArrayRepeat(value, length) => {
                if !(1..=MAX_ARRAY_LEN).contains(length) {
                    return Err(self.error(format!(
                        "array length must be between 1 and {MAX_ARRAY_LEN}"
                    )));
                }
                let value = self.expr(value, initialized)?;
                let element = value
                    .scalar()
                    .ok_or_else(|| self.error("array elements must be scalar"))?;
                Type::Array(element, *length)
            }
            IrExprKind::Index(array, index) => {
                let array = self.expr(array, initialized)?;
                let index = self.expr(index, initialized)?;
                self.require(index, Type::Num, "array index")?;
                let Type::Array(element, _) = array else {
                    return Err(self.error("indexing requires an array"));
                };
                element.typ()
            }
            IrExprKind::Len(array) => {
                let array = self.expr(array, initialized)?;
                if !matches!(array, Type::Array(..)) {
                    return Err(self.error("len requires an array"));
                }
                Type::Num
            }
        };
        if actual != expression.typ {
            return Err(self.error(format!(
                "expression annotation is {}, inferred {}",
                expression.typ, actual
            )));
        }
        Ok(actual)
    }

    /// Returns true only if every path through the block returns. Initialization
    /// describes the paths that can still fall through to the next statement.
    fn block(&self, statements: &[IrStmt], initialized: &mut Vec<bool>) -> Result<bool, String> {
        let mut returns = false;
        for (index, statement) in statements.iter().enumerate() {
            if returns {
                return Err(self.error(format!(
                    "unreachable statement {index} after unconditional return"
                )));
            }
            match statement {
                IrStmt::Drop(slot) => {
                    self.require(self.local_type(*slot)?, Type::Buffer, "drop local")?;
                    initialized[*slot] = false;
                }
                IrStmt::BufferStore { slot, index, value } => {
                    self.buffer_local(*slot, initialized)?;
                    let index = self.expr(index, initialized)?;
                    self.require(index, Type::Num, "buffer index")?;
                    self.buffer_local(*slot, initialized)?;
                    let value = self.expr(value, initialized)?;
                    self.require(value, Type::Num, "buffer element store")?;
                    self.buffer_local(*slot, initialized)?;
                }
                IrStmt::Store(slot, value) => {
                    let expected = self.local_type(*slot)?;
                    // Read the RHS before marking its destination initialized.
                    let actual = self.expr(value, initialized)?;
                    self.require(actual, expected, &format!("store to local slot {slot}"))?;
                    initialized[*slot] = true;
                }
                IrStmt::StorePlace { place, value } => {
                    let mut typ = self.local_type(place.slot)?;
                    if !initialized[place.slot] {
                        return Err(self.error(format!(
                            "aggregate slot {} is not definitely initialized",
                            place.slot
                        )));
                    }
                    if place.projections.is_empty() {
                        return Err(self.error("projected store requires at least one projection"));
                    }
                    for projection in &place.projections {
                        match projection {
                            IrProjection::Field(field) => {
                                let Type::Record { id, .. } = typ else {
                                    return Err(
                                        self.error("field store projection requires a record")
                                    );
                                };
                                typ = self.program.records[id]
                                    .fields
                                    .get(*field)
                                    .ok_or_else(|| {
                                        self.error(format!(
                                            "record field index {field} is out of bounds"
                                        ))
                                    })?
                                    .typ;
                            }
                            IrProjection::Index(index) => {
                                let actual = self.expr(index, initialized)?;
                                self.require(actual, Type::Num, "array index")?;
                                let Type::Array(element, _) = typ else {
                                    return Err(self.error("indexed store requires an array slot"));
                                };
                                typ = element.typ();
                            }
                        }
                    }
                    let actual = self.expr(value, initialized)?;
                    self.require(actual, typ, "indexed store element or record field")?;
                }
                IrStmt::Say(value) => {
                    let actual = self.expr(value, initialized)?;
                    if actual.scalar().is_none() {
                        return Err(self.error("say requires a scalar"));
                    }
                }
                IrStmt::Return(value) => {
                    let actual = self.expr(value, initialized)?;
                    self.require(actual, self.function.returns, "return value")?;
                    returns = true;
                }
                IrStmt::If { condition, yes, no } => {
                    let actual = self.expr(condition, initialized)?;
                    self.require(actual, Type::Flag, "if condition")?;
                    let mut yes_initialized = initialized.clone();
                    let mut no_initialized = initialized.clone();
                    let yes_returns = self.block(yes, &mut yes_initialized)?;
                    let no_returns = self.block(no, &mut no_initialized)?;
                    match (yes_returns, no_returns) {
                        (true, true) => returns = true,
                        (true, false) => *initialized = no_initialized,
                        (false, true) => *initialized = yes_initialized,
                        (false, false) => {
                            for ((state, yes), no) in initialized
                                .iter_mut()
                                .zip(yes_initialized)
                                .zip(no_initialized)
                            {
                                *state = yes && no;
                            }
                        }
                    }
                }
                IrStmt::While { condition, body } => {
                    let before_condition = initialized.clone();
                    let actual = self.expr(condition, initialized)?;
                    self.require(actual, Type::Flag, "while condition")?;
                    for (slot, typ) in self.function.locals.iter().enumerate() {
                        if *typ == Type::Buffer && before_condition[slot] != initialized[slot] {
                            return Err(self.error("loop condition cannot consume a buffer local"));
                        }
                    }
                    let mut body_initialized = initialized.clone();
                    let body_returns = self.block(body, &mut body_initialized)?;
                    if !body_returns {
                        for (slot, typ) in self.function.locals.iter().enumerate() {
                            if *typ == Type::Buffer && initialized[slot] && !body_initialized[slot]
                            {
                                return Err(self.error(format!(
                                    "buffer local {slot} is moved across a loop backedge"
                                )));
                            }
                        }
                    }
                    // The loop can execute zero times, including when a future
                    // optimization changes its condition. Body-only stores do
                    // not initialize slots on the fallthrough path.
                }
            }
        }
        Ok(returns)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn literal(literal: Literal) -> IrExpr {
        let typ = match &literal {
            Literal::Num(_) => Type::Num,
            Literal::Flag(_) => Type::Flag,
            Literal::Text(_) => Type::Text,
        };
        IrExpr {
            kind: IrExprKind::Literal(literal),
            typ,
            span: Span::default(),
        }
    }

    fn num(value: i64) -> IrExpr {
        literal(Literal::Num(value))
    }

    fn flag(value: bool) -> IrExpr {
        literal(Literal::Flag(value))
    }

    fn local(slot: usize, typ: Type) -> IrExpr {
        IrExpr {
            kind: IrExprKind::Local(slot),
            typ,
            span: Span::default(),
        }
    }

    fn program(locals: Vec<Type>, body: Vec<IrStmt>) -> IrProgram {
        IrProgram {
            records: vec![],
            main: 0,
            functions: vec![IrFunction {
                name: "main".to_owned(),
                params: vec![],
                returns: Type::Num,
                locals,
                body,
            }],
        }
    }

    fn rejects(program: &IrProgram, context: &str) {
        let error = verify(program).expect_err("malformed IR must fail");
        assert!(
            error.contains(context),
            "expected {context:?}, got {error:?}"
        );
    }

    fn buffer(length: IrExpr) -> IrExpr {
        IrExpr {
            kind: IrExprKind::Buffer(Box::new(length)),
            typ: Type::Buffer,
            span: Span::default(),
        }
    }

    fn buffer_len(slot: usize) -> IrExpr {
        IrExpr {
            kind: IrExprKind::BufferLen { slot },
            typ: Type::Num,
            span: Span::default(),
        }
    }

    #[test]
    fn buffers_move_and_reinitialize_without_implicit_copies() {
        let mut ir = program(
            vec![Type::Buffer, Type::Buffer],
            vec![
                IrStmt::Store(0, buffer(num(2))),
                IrStmt::Store(1, local(0, Type::Buffer)),
                IrStmt::Say(buffer_len(0)),
                IrStmt::Return(num(0)),
            ],
        );
        rejects(&ir, "not definitely available");
        ir.functions[0]
            .body
            .insert(2, IrStmt::Store(0, buffer(num(0))));
        verify(&ir).unwrap();
        ir.functions[0].body.insert(3, IrStmt::Drop(0));
        rejects(&ir, "not definitely available");
    }

    #[test]
    fn buffers_check_all_fallthrough_paths_and_loop_backedges() {
        let mut ir = program(
            vec![Type::Buffer, Type::Buffer],
            vec![
                IrStmt::Store(0, buffer(num(1))),
                IrStmt::If {
                    condition: flag(true),
                    yes: vec![IrStmt::Store(1, local(0, Type::Buffer))],
                    no: vec![],
                },
                IrStmt::Say(buffer_len(0)),
                IrStmt::Return(num(0)),
            ],
        );
        rejects(&ir, "not definitely available");
        ir.functions[0].body[1] = IrStmt::If {
            condition: flag(true),
            yes: vec![
                IrStmt::Store(1, local(0, Type::Buffer)),
                IrStmt::Return(num(0)),
            ],
            no: vec![],
        };
        verify(&ir).unwrap();
        ir.functions[0].body[1] = IrStmt::While {
            condition: flag(false),
            body: vec![IrStmt::Store(1, local(0, Type::Buffer))],
        };
        rejects(&ir, "loop backedge");
    }

    #[test]
    fn buffers_cannot_hide_in_value_records_or_output_as_pointers() {
        let mut ir = program(
            vec![Type::Buffer],
            vec![
                IrStmt::Store(0, buffer(num(1))),
                IrStmt::Say(local(0, Type::Buffer)),
                IrStmt::Return(num(0)),
            ],
        );
        rejects(&ir, "say requires a scalar");
        ir.functions[0].body.remove(1);
        ir.records.push(IrRecord {
            name: "Owner".into(),
            words: 1,
            fields: vec![IrField {
                name: "data".into(),
                typ: Type::Buffer,
                offset: 0,
            }],
        });
        rejects(&ir, "cannot contain an owned buffer");
    }

    #[test]
    fn buffer_allocation_and_index_types_are_verified() {
        let mut ir = program(
            vec![Type::Buffer],
            vec![IrStmt::Store(0, buffer(flag(true))), IrStmt::Return(num(0))],
        );
        rejects(&ir, "buffer length expects num");
        ir.functions[0].body[0] = IrStmt::Store(0, buffer(num(1)));
        ir.functions[0].body.insert(
            1,
            IrStmt::BufferStore {
                slot: 0,
                index: flag(false),
                value: num(3),
            },
        );
        rejects(&ir, "buffer index expects num");
        ir.functions[0].body[1] = IrStmt::BufferStore {
            slot: 0,
            index: num(0),
            value: flag(false),
        };
        rejects(&ir, "buffer element store expects num");
    }

    #[test]
    fn validates_entry_and_function_layout() {
        let mut ir = program(vec![], vec![IrStmt::Return(num(0))]);
        verify(&ir).unwrap();
        ir.main = 1;
        rejects(&ir, "main function index");
        ir.main = 0;
        ir.functions[0].returns = Type::Flag;
        rejects(&ir, "entry signature");
        ir.functions[0].returns = Type::Num;
        ir.functions.push(IrFunction {
            name: "helper".into(),
            params: vec![Type::Num],
            returns: Type::Num,
            locals: vec![Type::Flag],
            body: vec![IrStmt::Return(num(0))],
        });
        rejects(&ir, "prefix of local slots");
        ir.functions[1].params = vec![Type::Num; 7];
        rejects(&ir, "six parameters");
    }

    #[test]
    fn checks_expression_annotations_and_operands() {
        let mut bad = num(1);
        bad.typ = Type::Flag;
        rejects(
            &program(vec![], vec![IrStmt::Say(bad), IrStmt::Return(num(0))]),
            "expression annotation",
        );
        let bad = IrExpr {
            kind: IrExprKind::Binary(Binary::Add, Box::new(num(1)), Box::new(flag(true))),
            typ: Type::Num,
            span: Span::default(),
        };
        rejects(
            &program(vec![], vec![IrStmt::Return(bad)]),
            "arithmetic right operand",
        );
        let bad = IrExpr {
            kind: IrExprKind::Unary(Unary::Not, Box::new(num(1))),
            typ: Type::Flag,
            span: Span::default(),
        };
        rejects(
            &program(vec![], vec![IrStmt::Say(bad), IrStmt::Return(num(0))]),
            "unary operand",
        );
        let text = literal(Literal::Text("x".into()));
        let bad = IrExpr {
            kind: IrExprKind::Binary(Binary::Eq, Box::new(text.clone()), Box::new(text)),
            typ: Type::Flag,
            span: Span::default(),
        };
        rejects(
            &program(vec![], vec![IrStmt::Say(bad), IrStmt::Return(num(0))]),
            "equality requires",
        );
    }

    #[test]
    fn rejects_bad_call_indices_arity_arguments_and_return_annotations() {
        let call = |index, args, typ| IrExpr {
            kind: IrExprKind::Call(index, args),
            typ,
            span: Span::default(),
        };
        rejects(
            &program(vec![], vec![IrStmt::Return(call(2, vec![], Type::Num))]),
            "call function index",
        );
        let mut ir = program(vec![], vec![IrStmt::Return(call(1, vec![], Type::Num))]);
        ir.functions.push(IrFunction {
            name: "helper".into(),
            params: vec![Type::Num],
            returns: Type::Num,
            locals: vec![Type::Num],
            body: vec![IrStmt::Return(local(0, Type::Num))],
        });
        rejects(&ir, "expects 1 arguments");
        ir.functions[0].body = vec![IrStmt::Return(call(1, vec![flag(true)], Type::Num))];
        rejects(&ir, "call 'helper' argument 1");
        ir.functions[0].body = vec![IrStmt::Return(call(1, vec![num(1)], Type::Flag))];
        rejects(&ir, "expression annotation");
        ir.functions[0].body = vec![IrStmt::Return(call(1, vec![num(1)], Type::Num))];
        verify(&ir).unwrap();
    }

    #[test]
    fn validates_local_bounds_store_types_and_initialization() {
        rejects(
            &program(vec![], vec![IrStmt::Return(local(0, Type::Num))]),
            "out of bounds",
        );
        rejects(
            &program(
                vec![],
                vec![IrStmt::Store(0, num(1)), IrStmt::Return(num(0))],
            ),
            "out of bounds",
        );
        rejects(
            &program(vec![Type::Num], vec![IrStmt::Return(local(0, Type::Num))]),
            "not definitely initialized",
        );
        rejects(
            &program(
                vec![Type::Num],
                vec![
                    IrStmt::Store(0, local(0, Type::Num)),
                    IrStmt::Return(num(0)),
                ],
            ),
            "not definitely initialized",
        );
        rejects(
            &program(
                vec![Type::Num],
                vec![IrStmt::Store(0, flag(true)), IrStmt::Return(num(0))],
            ),
            "store to local slot 0",
        );
        rejects(
            &program(
                vec![Type::Num],
                vec![
                    IrStmt::Store(0, num(1)),
                    IrStmt::Return(local(0, Type::Flag)),
                ],
            ),
            "expression annotation",
        );
        verify(&program(
            vec![Type::Num],
            vec![
                IrStmt::Store(0, num(1)),
                IrStmt::Return(local(0, Type::Num)),
            ],
        ))
        .unwrap();
    }

    #[test]
    fn joins_initialization_only_across_falling_branches() {
        let conditional = |yes, no| IrStmt::If {
            condition: flag(true),
            yes,
            no,
        };
        let mut ir = program(
            vec![Type::Num],
            vec![
                conditional(vec![IrStmt::Store(0, num(1))], vec![]),
                IrStmt::Return(local(0, Type::Num)),
            ],
        );
        rejects(&ir, "not definitely initialized");
        ir.functions[0].body[0] = conditional(
            vec![IrStmt::Store(0, num(1))],
            vec![IrStmt::Store(0, num(2))],
        );
        verify(&ir).unwrap();
        ir.functions[0].body[0] =
            conditional(vec![IrStmt::Return(num(1))], vec![IrStmt::Store(0, num(2))]);
        verify(&ir).unwrap();
        ir.functions[0].body[0] =
            conditional(vec![IrStmt::Store(0, num(1))], vec![IrStmt::Return(num(2))]);
        verify(&ir).unwrap();
    }

    #[test]
    fn loops_do_not_export_initialization_but_validate_first_iteration() {
        let mut ir = program(
            vec![Type::Num],
            vec![
                IrStmt::While {
                    condition: flag(true),
                    body: vec![IrStmt::Store(0, num(1))],
                },
                IrStmt::Return(local(0, Type::Num)),
            ],
        );
        rejects(&ir, "not definitely initialized");
        ir.functions[0].body = vec![
            IrStmt::While {
                condition: flag(false),
                body: vec![IrStmt::Say(local(0, Type::Num)), IrStmt::Store(0, num(1))],
            },
            IrStmt::Return(num(0)),
        ];
        rejects(&ir, "not definitely initialized");
        ir.functions[0].body = vec![
            IrStmt::Store(0, num(0)),
            IrStmt::While {
                condition: flag(true),
                body: vec![IrStmt::Store(0, num(1))],
            },
            IrStmt::Return(local(0, Type::Num)),
        ];
        verify(&ir).unwrap();
    }

    #[test]
    fn verifies_control_flow_returns_and_conditions() {
        rejects(&program(vec![], vec![]), "does not return");
        rejects(
            &program(vec![], vec![IrStmt::Return(flag(true))]),
            "return value",
        );
        rejects(
            &program(vec![], vec![IrStmt::Return(num(0)), IrStmt::Say(num(1))]),
            "unreachable",
        );
        rejects(
            &program(
                vec![],
                vec![
                    IrStmt::If {
                        condition: num(1),
                        yes: vec![],
                        no: vec![],
                    },
                    IrStmt::Return(num(0)),
                ],
            ),
            "if condition",
        );
        rejects(
            &program(
                vec![],
                vec![
                    IrStmt::While {
                        condition: num(1),
                        body: vec![],
                    },
                    IrStmt::Return(num(0)),
                ],
            ),
            "while condition",
        );
        rejects(
            &program(
                vec![],
                vec![IrStmt::While {
                    condition: flag(true),
                    body: vec![IrStmt::Return(num(0))],
                }],
            ),
            "does not return",
        );
        verify(&program(
            vec![],
            vec![IrStmt::If {
                condition: flag(true),
                yes: vec![IrStmt::Return(num(1))],
                no: vec![IrStmt::Return(num(2))],
            }],
        ))
        .unwrap();
    }

    #[test]
    fn validates_source_and_optimizer_results() {
        for source in [
            include_str!("../examples/hello.vela"),
            include_str!("../examples/loops.vela"),
            include_str!("../examples/fibonacci.vela"),
            "craft main() -> num:\n    keep x = 7\n    when true:\n        keep x = 8\n        say x\n    otherwise:\n        say 0\n    say x\n    repeat false:\n        say 2\n    give 0\n",
        ] {
            let mut ir = crate::compile(source, false).unwrap();
            verify(&ir).unwrap();
            crate::optimize::run(&mut ir);
            verify(&ir).unwrap();
        }
    }

    fn array(values: Vec<IrExpr>, element: ScalarType) -> IrExpr {
        IrExpr {
            typ: Type::Array(element, values.len()),
            kind: IrExprKind::Array(values),
            span: Span::default(),
        }
    }

    #[test]
    fn validates_array_shapes_elements_and_repeat_counts() {
        let valid = array(vec![num(1), num(2)], ScalarType::Num);
        rejects(
            &program(
                vec![],
                vec![IrStmt::Store(0, valid.clone()), IrStmt::Return(num(0))],
            ),
            "out of bounds",
        );
        verify(&program(
            vec![valid.typ],
            vec![IrStmt::Store(0, valid.clone()), IrStmt::Return(num(0))],
        ))
        .unwrap();
        let mut mismatched = valid.clone();
        mismatched.typ = Type::Array(ScalarType::Num, 3);
        rejects(
            &program(
                vec![mismatched.typ],
                vec![IrStmt::Store(0, mismatched), IrStmt::Return(num(0))],
            ),
            "expression annotation",
        );
        let mixed = array(vec![num(1), flag(true)], ScalarType::Num);
        rejects(
            &program(
                vec![mixed.typ],
                vec![IrStmt::Store(0, mixed), IrStmt::Return(num(0))],
            ),
            "array literal element",
        );
        let repeated = |length| IrExpr {
            typ: Type::Array(ScalarType::Num, 1),
            kind: IrExprKind::ArrayRepeat(Box::new(num(1)), length),
            span: Span::default(),
        };
        for length in [0, usize::MAX] {
            rejects(
                &program(
                    vec![Type::Array(ScalarType::Num, 1)],
                    vec![IrStmt::Store(0, repeated(length)), IrStmt::Return(num(0))],
                ),
                "array length",
            );
        }
        for length in [0, MAX_ARRAY_LEN + 1, usize::MAX] {
            rejects(
                &program(
                    vec![Type::Array(ScalarType::Num, length)],
                    vec![IrStmt::Return(num(0))],
                ),
                "array length",
            );
        }
    }

    #[test]
    fn array_index_store_requires_initialized_array_and_scalar_index_value() {
        let typ = Type::Array(ScalarType::Num, 1);
        let store = |index, value| IrStmt::StorePlace {
            place: IrPlace {
                slot: 0,
                projections: vec![IrProjection::Index(index)],
            },
            value,
        };
        rejects(
            &program(
                vec![typ],
                vec![store(num(0), num(2)), IrStmt::Return(num(0))],
            ),
            "not definitely initialized",
        );
        let initialize = IrStmt::Store(0, array(vec![num(1)], ScalarType::Num));
        rejects(
            &program(
                vec![typ],
                vec![
                    initialize.clone(),
                    store(flag(true), num(2)),
                    IrStmt::Return(num(0)),
                ],
            ),
            "array index",
        );
        rejects(
            &program(
                vec![typ],
                vec![
                    initialize.clone(),
                    store(num(0), flag(true)),
                    IrStmt::Return(num(0)),
                ],
            ),
            "indexed store element",
        );
        verify(&program(
            vec![typ],
            vec![initialize, store(num(-1), num(2)), IrStmt::Return(num(0))],
        ))
        .unwrap();
    }

    #[test]
    fn array_index_length_and_print_require_their_declared_types() {
        let a = array(vec![num(1)], ScalarType::Num);
        let index = |array, index, typ| IrExpr {
            kind: IrExprKind::Index(Box::new(array), Box::new(index)),
            typ,
            span: Span::default(),
        };
        rejects(
            &program(
                vec![],
                vec![
                    IrStmt::Say(index(a.clone(), flag(false), Type::Num)),
                    IrStmt::Return(num(0)),
                ],
            ),
            "array index",
        );
        rejects(
            &program(
                vec![],
                vec![
                    IrStmt::Say(index(num(0), num(0), Type::Num)),
                    IrStmt::Return(num(0)),
                ],
            ),
            "indexing requires an array",
        );
        rejects(
            &program(vec![], vec![IrStmt::Say(a), IrStmt::Return(num(0))]),
            "say requires a scalar",
        );
        let len = IrExpr {
            kind: IrExprKind::Len(Box::new(num(1))),
            typ: Type::Num,
            span: Span::default(),
        };
        rejects(
            &program(vec![], vec![IrStmt::Say(len), IrStmt::Return(num(0))]),
            "len requires an array",
        );
    }

    #[test]
    fn frame_estimate_can_exceed_native_capacity_but_fixed_locals_cannot() {
        let typ = Type::Array(ScalarType::Num, MAX_ARRAY_LEN);
        let mut ir = program(vec![typ], vec![IrStmt::Return(num(0))]);
        assert_eq!(frame_words(&ir.functions[0]).unwrap(), MAX_ARRAY_LEN + 1);
        let len = || IrExpr {
            kind: IrExprKind::Len(Box::new(local(0, typ))),
            typ: Type::Num,
            span: Span::default(),
        };
        ir.functions[0]
            .body
            .splice(0..0, (0..14).map(|_| IrStmt::Say(len())));
        assert_eq!(
            frame_words(&ir.functions[0]).unwrap(),
            MAX_ARRAY_LEN * 15 + 1
        );
        ir.functions[0].body.insert(0, IrStmt::Say(len()));
        assert!(frame_words(&ir.functions[0]).unwrap() > MAX_FRAME_WORDS);
        ir.functions[0].locals = vec![typ; 17];
        assert!(frame_words(&ir.functions[0])
            .unwrap_err()
            .contains("fixed local storage exceeds"));
    }

    fn record_program() -> IrProgram {
        let mut ir = program(vec![], vec![IrStmt::Return(num(0))]);
        ir.records = vec![IrRecord {
            name: "Point".into(),
            words: 2,
            fields: vec![
                IrField {
                    name: "x".into(),
                    typ: Type::Num,
                    offset: 0,
                },
                IrField {
                    name: "y".into(),
                    typ: Type::Num,
                    offset: 1,
                },
            ],
        }];
        ir
    }
    fn point(fields: Vec<(usize, IrExpr)>) -> IrExpr {
        IrExpr {
            typ: Type::Record { id: 0, words: 2 },
            kind: IrExprKind::Record { record: 0, fields },
            span: Span::default(),
        }
    }

    #[test]
    fn records_verify_canonical_layouts_offsets_cycles_and_width_caches() {
        verify(&record_program()).unwrap();
        let mut ir = record_program();
        ir.records[0].fields[1].offset = 0;
        rejects(&ir, "offset is not contiguous");
        let mut ir = record_program();
        ir.records[0].fields[1].name = "x".into();
        rejects(&ir, "duplicate field");
        let mut ir = record_program();
        ir.records[0].words = 3;
        rejects(&ir, "layout width");
        let mut ir = record_program();
        ir.functions[0]
            .locals
            .push(Type::Record { id: 0, words: 1 });
        rejects(&ir, "cached record width");
        ir.functions[0].locals[0] = Type::Record { id: 1, words: 2 };
        rejects(&ir, "record id 1 is out of bounds");
        let mut ir = record_program();
        ir.records[0] = IrRecord {
            name: "Loop".into(),
            words: 1,
            fields: vec![IrField {
                name: "again".into(),
                typ: Type::Record { id: 0, words: 1 },
                offset: 0,
            }],
        };
        rejects(&ir, "record layout cycle");
    }

    #[test]
    fn record_initializers_and_field_reads_reject_malformed_ir() {
        let valid = point(vec![(1, num(20)), (0, num(10))]);
        let typ = valid.typ;
        let mut ir = record_program();
        ir.functions[0].locals.push(typ);
        ir.functions[0].body.insert(0, IrStmt::Store(0, valid));
        verify(&ir).unwrap();
        for (value, context) in [
            (point(vec![(0, num(1))]), "missing record field"),
            (
                point(vec![(0, num(1)), (0, num(2))]),
                "duplicate record field",
            ),
            (
                point(vec![(0, num(1)), (5, num(2))]),
                "field index 5 is out of bounds",
            ),
            (
                point(vec![(0, flag(false)), (1, num(2))]),
                "record field initializer",
            ),
        ] {
            ir.functions[0].body[0] = IrStmt::Store(0, value);
            rejects(&ir, context);
        }
        let field = |base, field, typ| IrExpr {
            kind: IrExprKind::Field {
                base: Box::new(base),
                field,
            },
            typ,
            span: Span::default(),
        };
        ir.functions[0].body = vec![
            IrStmt::Say(field(point(vec![(0, num(1)), (1, num(2))]), 2, Type::Num)),
            IrStmt::Return(num(0)),
        ];
        rejects(&ir, "field index 2 is out of bounds");
        ir.functions[0].body[0] = IrStmt::Say(field(num(1), 0, Type::Num));
        rejects(&ir, "field access requires a record");
    }

    #[test]
    fn projected_record_stores_require_initialized_complete_values_and_valid_paths() {
        let typ = Type::Record { id: 0, words: 2 };
        let mut ir = record_program();
        ir.functions[0].locals.push(typ);
        let store = |projections, value| IrStmt::StorePlace {
            place: IrPlace {
                slot: 0,
                projections,
            },
            value,
        };
        ir.functions[0]
            .body
            .insert(0, store(vec![IrProjection::Field(0)], num(4)));
        rejects(&ir, "not definitely initialized");
        ir.functions[0]
            .body
            .insert(0, IrStmt::Store(0, point(vec![(0, num(1)), (1, num(2))])));
        verify(&ir).unwrap();
        ir.functions[0].body[1] = store(vec![IrProjection::Field(0)], flag(false));
        rejects(&ir, "record field");
        ir.functions[0].body[1] = store(vec![IrProjection::Field(9)], num(1));
        rejects(&ir, "field index 9 is out of bounds");
        ir.functions[0].body[1] = store(
            vec![IrProjection::Field(0), IrProjection::Index(num(0))],
            num(1),
        );
        rejects(&ir, "indexed store requires an array");
        ir.functions[0].body[1] = store(vec![], num(1));
        rejects(&ir, "requires at least one projection");
    }
}
