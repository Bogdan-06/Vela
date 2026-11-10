//! Direct x86-64 GNU assembly generation. GCC is only an assembler/linker driver.
use crate::model::*;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target {
    Windows,
    Linux,
}

impl Target {
    pub fn host() -> Result<Self, String> {
        if !cfg!(target_arch = "x86_64") {
            return Err("native code generation currently requires an x86-64 host".into());
        }
        if cfg!(target_os = "windows") {
            Ok(Self::Windows)
        } else if cfg!(target_os = "linux") {
            Ok(Self::Linux)
        } else {
            Err("native code generation currently supports Windows and Linux only".into())
        }
    }
}

struct Generator<'a> {
    records: &'a [IrRecord],
    target: Target,
    lines: Vec<String>,
    strings: BTreeMap<String, String>,
    label_counter: usize,
    /// Number of temporary eight-byte values beneath the aligned fixed frame.
    depth: usize,
    return_label: String,
    frame: Frame,
}

/// Every aggregate rvalue owns a fixed buffer in this activation. Expression
/// identities are stable while generating an immutable IR program, including
/// when the same source expression executes repeatedly inside a loop.
#[derive(Default)]
struct Frame {
    locals: Vec<usize>,
    local_types: Vec<Type>,
    arrays: BTreeMap<usize, usize>,
    words: usize,
    result_pointer: Option<usize>,
}

impl Frame {
    fn allocate(&mut self, words: usize) -> usize {
        self.words += words;
        self.words * 8
    }

    fn new(function: &IrFunction) -> Self {
        let mut frame = Self {
            local_types: function.locals.clone(),
            ..Self::default()
        };
        for typ in &function.locals {
            let offset = frame.allocate(typ.words());
            frame.locals.push(offset);
        }
        frame.block(&function.body);
        if function.returns.aggregate() {
            frame.result_pointer = Some(frame.allocate(1));
        }
        frame
    }

    fn expr(&mut self, expr: &IrExpr) {
        if expr.typ.aggregate() {
            let offset = self.allocate(expr.typ.words());
            self.arrays.insert(expr as *const IrExpr as usize, offset);
        }
        match &expr.kind {
            IrExprKind::Unary(_, child)
            | IrExprKind::Len(child)
            | IrExprKind::ArrayRepeat(child, _) => self.expr(child),
            IrExprKind::Binary(_, left, right) | IrExprKind::Index(left, right) => {
                self.expr(left);
                self.expr(right);
            }
            IrExprKind::Call(_, args) | IrExprKind::Array(args) => {
                for arg in args {
                    self.expr(arg);
                }
            }
            IrExprKind::Record { fields, .. } => {
                for (_, value) in fields {
                    self.expr(value);
                }
            }
            IrExprKind::Field { base, .. } => self.expr(base),
            IrExprKind::Literal(_) | IrExprKind::Local(_) => {}
            IrExprKind::Buffer(_)
            | IrExprKind::BufferCopy { .. }
            | IrExprKind::BufferLen { .. }
            | IrExprKind::BufferGet { .. } => {
                panic!("owned buffers require the verified CFG backend")
            }
        }
    }

    fn block(&mut self, body: &[IrStmt]) {
        for statement in body {
            match statement {
                IrStmt::Drop(_) | IrStmt::BufferStore { .. } => {
                    panic!("owned buffers require the verified CFG backend")
                }
                IrStmt::Store(_, value) | IrStmt::Say(value) | IrStmt::Return(value) => {
                    self.expr(value)
                }
                IrStmt::StorePlace { place, value } => {
                    for projection in &place.projections {
                        if let IrProjection::Index(index) = projection {
                            self.expr(index);
                        }
                    }
                    self.expr(value);
                }
                IrStmt::If { condition, yes, no } => {
                    self.expr(condition);
                    self.block(yes);
                    self.block(no);
                }
                IrStmt::While { condition, body } => {
                    self.expr(condition);
                    self.block(body);
                }
            }
        }
    }

    fn array(&self, expr: &IrExpr) -> usize {
        self.arrays[&(expr as *const IrExpr as usize)]
    }
}

impl Generator<'_> {
    fn emit(&mut self, line: impl Into<String>) {
        self.lines.push(line.into());
    }

    fn label(&mut self, prefix: &str) -> String {
        let label = format!(".Lvela_{}_{}", prefix, self.label_counter);
        self.label_counter += 1;
        label
    }

    fn push(&mut self) {
        self.emit("    pushq %rax");
        self.depth += 1;
    }

    fn pop(&mut self, register: &str) {
        self.emit(format!("    popq {register}"));
        self.depth -= 1;
    }

    fn registers(&self) -> &'static [&'static str] {
        match self.target {
            Target::Windows => &["%rcx", "%rdx", "%r8", "%r9"],
            Target::Linux => &["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"],
        }
    }

    /// The top `arguments` temporary values are ordered in source order, oldest
    /// first. Preserve other temporaries and ensure rsp is 16-byte aligned at call.
    fn call(&mut self, name: &str, arguments: usize, variadic: bool) {
        let registers = self.registers();
        let stack_arguments = arguments.saturating_sub(registers.len());
        let shadow = if self.target == Target::Windows {
            32
        } else {
            0
        };
        let required = shadow + stack_arguments * 8;
        let padding = (16 - (self.depth * 8 + required) % 16) % 16;
        let reserved = required + padding;
        if reserved != 0 {
            self.emit(format!("    subq ${reserved}, %rsp"));
        }
        // Copy stack arguments before loading argument registers. r11 is volatile
        // on both ABIs and not an integer argument register on either target.
        for index in registers.len()..arguments {
            let source = reserved + (arguments - 1 - index) * 8;
            let destination = shadow + (index - registers.len()) * 8;
            self.emit(format!("    movq {source}(%rsp), %r11"));
            self.emit(format!("    movq %r11, {destination}(%rsp)"));
        }
        for (index, register) in registers.iter().take(arguments).enumerate() {
            let source = reserved + (arguments - 1 - index) * 8;
            self.emit(format!("    movq {source}(%rsp), {register}"));
        }
        if variadic && self.target == Target::Linux {
            // SysV varargs: no vector arguments.
            self.emit("    xorl %eax, %eax");
        }
        self.emit(format!("    call {name}"));
        let released = reserved + arguments * 8;
        if released != 0 {
            self.emit(format!("    addq ${released}, %rsp"));
        }
        self.depth -= arguments;
    }

    fn string(&mut self, value: &str) -> String {
        if let Some(label) = self.strings.get(value) {
            return label.clone();
        }
        let label = self.label("text");
        self.strings.insert(value.to_owned(), label.clone());
        label
    }

    /// Copy a value from rax to r10. Only volatile registers are used on both
    /// supported ABIs; all incoming arguments are spilled before this is used.
    fn copy_array(&mut self, words: usize) {
        let begin = self.label("array_copy");
        self.emit("    xorl %r11d, %r11d");
        self.emit(format!("{begin}:"));
        self.emit("    movq (%rax,%r11,8), %rcx");
        self.emit("    movq %rcx, (%r10,%r11,8)");
        self.emit("    incq %r11");
        self.emit(format!("    cmpq ${words}, %r11"));
        self.emit(format!("    jb {begin}"));
        self.emit("    movq %r10, %rax");
    }

    /// Unsigned comparison rejects both negative and upper-bound indices.
    fn check_index(&mut self, length: usize) {
        self.emit(format!("    cmpq ${length}, %rax"));
        self.emit("    jae .Lvela_bounds_fault");
    }

    /// A field chain rooted in a local has no evaluation effects and can be
    /// addressed without materializing a value copy of each containing record.
    fn local_address_offset(&self, expression: &IrExpr) -> Option<usize> {
        match &expression.kind {
            IrExprKind::Local(slot) => Some(self.frame.locals[*slot]),
            IrExprKind::Field { base, field } => {
                let Type::Record { id, .. } = base.typ else {
                    return None;
                };
                let offset = self.local_address_offset(base)?;
                Some(offset - self.records[id].fields[*field].offset * 8)
            }
            _ => None,
        }
    }

    /// Evaluate a mutable place's projection indices before the assignment RHS.
    /// Every index is checked before progressing; the resulting address stays
    /// private to this compiler operation and never becomes a source value.
    fn place_address(&mut self, place: &IrPlace) -> Type {
        let offset = self.frame.locals[place.slot];
        let mut typ = self.frame.local_types[place.slot];
        self.emit(format!("    leaq -{offset}(%rbp), %rax"));
        for projection in &place.projections {
            match projection {
                IrProjection::Field(field) => {
                    let Type::Record { id, .. } = typ else {
                        unreachable!("verified record place")
                    };
                    let field = &self.records[id].fields[*field];
                    let bytes = field.offset * 8;
                    typ = field.typ;
                    if bytes != 0 {
                        self.emit(format!("    addq ${bytes}, %rax"));
                    }
                }
                IrProjection::Index(index) => {
                    let Type::Array(element, length) = typ else {
                        unreachable!("verified array place")
                    };
                    self.push();
                    self.expression(index);
                    self.check_index(length);
                    self.pop("%r10");
                    self.emit("    leaq (%r10,%rax,8), %rax");
                    typ = element.typ();
                }
            }
        }
        typ
    }

    fn expression(&mut self, expression: &IrExpr) {
        match &expression.kind {
            IrExprKind::Buffer(_)
            | IrExprKind::BufferCopy { .. }
            | IrExprKind::BufferLen { .. }
            | IrExprKind::BufferGet { .. } => {
                panic!("owned buffers require the verified CFG backend")
            }
            IrExprKind::Literal(Literal::Num(value)) => {
                self.emit(format!("    movabsq ${value}, %rax"));
            }
            IrExprKind::Literal(Literal::Flag(value)) => {
                self.emit(format!("    movq ${}, %rax", usize::from(*value)));
            }
            IrExprKind::Literal(Literal::Text(value)) => {
                let label = self.string(value);
                self.emit(format!("    leaq {label}(%rip), %rax"));
            }
            IrExprKind::Local(index) => {
                let offset = self.frame.locals[*index];
                if expression.typ.aggregate() {
                    let words = expression.typ.words();
                    let temporary = self.frame.array(expression);
                    self.emit(format!("    leaq -{offset}(%rbp), %rax"));
                    self.emit(format!("    leaq -{temporary}(%rbp), %r10"));
                    self.copy_array(words);
                } else {
                    self.emit(format!("    movq -{offset}(%rbp), %rax"));
                }
            }
            IrExprKind::Unary(operator, value) => {
                self.expression(value);
                match operator {
                    Unary::Neg => {
                        self.emit("    negq %rax");
                        self.emit("    jo .Lvela_runtime_fault");
                    }
                    Unary::Not => {
                        self.emit("    testq %rax, %rax");
                        self.emit("    sete %al");
                        self.emit("    movzbq %al, %rax");
                    }
                }
            }
            IrExprKind::Binary(operator @ (Binary::And | Binary::Or), left, right) => {
                let done = self.label("short_circuit");
                self.expression(left);
                self.emit("    testq %rax, %rax");
                self.emit(format!(
                    "    {} {done}",
                    if *operator == Binary::And {
                        "je"
                    } else {
                        "jne"
                    }
                ));
                self.expression(right);
                self.emit(format!("{done}:"));
            }
            IrExprKind::Binary(operator, left, right) => {
                self.expression(left);
                self.push();
                self.expression(right);
                self.emit("    movq %rax, %r10");
                self.pop("%rax");
                match operator {
                    Binary::Add | Binary::Sub | Binary::Mul => {
                        let instruction = match operator {
                            Binary::Add => "addq",
                            Binary::Sub => "subq",
                            _ => "imulq",
                        };
                        self.emit(format!("    {instruction} %r10, %rax"));
                        self.emit("    jo .Lvela_runtime_fault");
                    }
                    Binary::Div | Binary::Rem => {
                        self.emit("    testq %r10, %r10");
                        self.emit("    je .Lvela_runtime_fault");
                        let safe = self.label("division_safe");
                        self.emit("    cmpq $-1, %r10");
                        self.emit(format!("    jne {safe}"));
                        self.emit("    movabsq $-9223372036854775808, %r11");
                        self.emit("    cmpq %r11, %rax");
                        self.emit("    je .Lvela_runtime_fault");
                        self.emit(format!("{safe}:"));
                        self.emit("    cqto");
                        self.emit("    idivq %r10");
                        if *operator == Binary::Rem {
                            self.emit("    movq %rdx, %rax");
                        }
                    }
                    Binary::Eq | Binary::Ne | Binary::Lt | Binary::Le | Binary::Gt | Binary::Ge => {
                        self.emit("    cmpq %r10, %rax");
                        let instruction = match operator {
                            Binary::Eq => "sete",
                            Binary::Ne => "setne",
                            Binary::Lt => "setl",
                            Binary::Le => "setle",
                            Binary::Gt => "setg",
                            Binary::Ge => "setge",
                            _ => unreachable!(),
                        };
                        self.emit(format!("    {instruction} %al"));
                        self.emit("    movzbq %al, %rax");
                    }
                    Binary::And | Binary::Or => unreachable!(),
                }
            }
            IrExprKind::Call(index, arguments) => {
                let aggregate = expression.typ.aggregate();
                if aggregate {
                    let offset = self.frame.array(expression);
                    self.emit(format!("    leaq -{offset}(%rbp), %rax"));
                    self.push();
                }
                for argument in arguments {
                    self.expression(argument);
                    self.push();
                }
                self.call(
                    &format!("v_fn_{index}"),
                    arguments.len() + usize::from(aggregate),
                    false,
                );
            }
            IrExprKind::Array(elements) => {
                let offset = self.frame.array(expression);
                for (index, element) in elements.iter().enumerate() {
                    self.expression(element);
                    self.emit(format!("    movq %rax, -{}(%rbp)", offset - index * 8));
                }
                self.emit(format!("    leaq -{offset}(%rbp), %rax"));
            }
            IrExprKind::ArrayRepeat(value, length) => {
                let offset = self.frame.array(expression);
                self.expression(value);
                let begin = self.label("array_repeat");
                self.emit(format!("    leaq -{offset}(%rbp), %r10"));
                self.emit("    xorl %r11d, %r11d");
                self.emit(format!("{begin}:"));
                self.emit("    movq %rax, (%r10,%r11,8)");
                self.emit("    incq %r11");
                self.emit(format!("    cmpq ${length}, %r11"));
                self.emit(format!("    jb {begin}"));
                self.emit("    movq %r10, %rax");
            }
            IrExprKind::Index(array, index) => {
                let Type::Array(_, length) = array.typ else {
                    unreachable!("checked array operand")
                };
                if let Some(offset) = self.local_address_offset(array) {
                    // Private local/field storage cannot be mutated by another
                    // function, so read-only indexing requires no value copy.
                    self.emit(format!("    leaq -{offset}(%rbp), %rax"));
                } else {
                    self.expression(array);
                }
                self.push();
                self.expression(index);
                self.check_index(length);
                self.pop("%r10");
                self.emit("    movq (%r10,%rax,8), %rax");
            }
            IrExprKind::Len(array) => {
                let Type::Array(_, length) = array.typ else {
                    unreachable!("checked len operand")
                };
                // A checked initialized local has no evaluation effects. Every
                // other operand must still execute (calls, faults, literal work).
                if self.local_address_offset(array).is_none() {
                    self.expression(array);
                }
                self.emit(format!("    movq ${length}, %rax"));
            }
            IrExprKind::Record { record, fields } => {
                let offset = self.frame.array(expression);
                for (field_index, value) in fields {
                    let field_offset = self.records[*record].fields[*field_index].offset;
                    self.expression(value);
                    let destination = offset - field_offset * 8;
                    if value.typ.aggregate() {
                        self.emit(format!("    leaq -{destination}(%rbp), %r10"));
                        self.copy_array(value.typ.words());
                    } else {
                        self.emit(format!("    movq %rax, -{destination}(%rbp)"));
                    }
                }
                self.emit(format!("    leaq -{offset}(%rbp), %rax"));
            }
            IrExprKind::Field { base, field } => {
                if let Some(offset) = self.local_address_offset(expression) {
                    self.emit(format!("    leaq -{offset}(%rbp), %rax"));
                } else {
                    let Type::Record { id, .. } = base.typ else {
                        unreachable!("verified record field")
                    };
                    let bytes = self.records[id].fields[*field].offset * 8;
                    self.expression(base);
                    if bytes != 0 {
                        self.emit(format!("    addq ${bytes}, %rax"));
                    }
                }
                if expression.typ.aggregate() {
                    let temporary = self.frame.array(expression);
                    self.emit(format!("    leaq -{temporary}(%rbp), %r10"));
                    self.copy_array(expression.typ.words());
                } else {
                    self.emit("    movq (%rax), %rax");
                }
            }
        }
    }

    fn block(&mut self, statements: &[IrStmt]) {
        for statement in statements {
            match statement {
                IrStmt::Drop(_) | IrStmt::BufferStore { .. } => {
                    panic!("owned buffers require the verified CFG backend")
                }
                IrStmt::Store(index, value) => {
                    self.expression(value);
                    let offset = self.frame.locals[*index];
                    if value.typ.aggregate() {
                        let words = value.typ.words();
                        self.emit(format!("    leaq -{offset}(%rbp), %r10"));
                        self.copy_array(words);
                    } else {
                        self.emit(format!("    movq %rax, -{offset}(%rbp)"));
                    }
                }
                IrStmt::StorePlace { place, value } => {
                    let destination_type = self.place_address(place);
                    self.push();
                    self.expression(value);
                    self.pop("%r10");
                    if destination_type.aggregate() {
                        self.copy_array(destination_type.words());
                    } else {
                        self.emit("    movq %rax, (%r10)");
                    }
                }
                IrStmt::Return(value) => {
                    self.expression(value);
                    if value.typ.aggregate() {
                        let words = value.typ.words();
                        let offset = self.frame.result_pointer.expect("aggregate result pointer");
                        self.emit(format!("    movq -{offset}(%rbp), %r10"));
                        self.copy_array(words);
                    }
                    self.emit(format!("    jmp {}", self.return_label));
                }
                IrStmt::Say(value) => {
                    self.expression(value);
                    match value.typ {
                        Type::Num => {
                            self.push();
                            // Reorder as printf(format, value), retaining source result.
                            self.emit("    leaq .Lvela_fmt_num(%rip), %rax");
                            self.push();
                            self.emit("    movq 8(%rsp), %r11");
                            self.emit("    movq %rax, 8(%rsp)");
                            self.emit("    movq %r11, (%rsp)");
                            self.call("printf", 2, true);
                        }
                        Type::Text => {
                            self.push();
                            self.call("puts", 1, false);
                        }
                        Type::Flag => {
                            let done = self.label("flag_print");
                            self.emit("    testq %rax, %rax");
                            self.emit("    leaq .Lvela_false(%rip), %rax");
                            self.emit(format!("    je {done}"));
                            self.emit("    leaq .Lvela_true(%rip), %rax");
                            self.emit(format!("{done}:"));
                            self.push();
                            self.call("puts", 1, false);
                        }
                        Type::Buffer | Type::Array(..) | Type::Record { .. } => {
                            unreachable!("aggregate output rejected by semantic analysis")
                        }
                    }
                }
                IrStmt::If { condition, yes, no } => {
                    let otherwise = self.label("otherwise");
                    let done = self.label("if_done");
                    self.expression(condition);
                    self.emit("    testq %rax, %rax");
                    self.emit(format!("    je {otherwise}"));
                    self.block(yes);
                    self.emit(format!("    jmp {done}"));
                    self.emit(format!("{otherwise}:"));
                    self.block(no);
                    self.emit(format!("{done}:"));
                }
                IrStmt::While { condition, body } => {
                    let begin = self.label("loop");
                    let done = self.label("loop_done");
                    self.emit(format!("{begin}:"));
                    self.expression(condition);
                    self.emit("    testq %rax, %rax");
                    self.emit(format!("    je {done}"));
                    self.block(body);
                    self.emit(format!("    jmp {begin}"));
                    self.emit(format!("{done}:"));
                }
            }
        }
    }

    fn function(&mut self, index: usize, function: &IrFunction) {
        self.depth = 0;
        self.frame = Frame::new(function);
        self.return_label = self.label("return");
        self.emit(format!("v_fn_{index}:"));
        self.emit("    pushq %rbp");
        self.emit("    movq %rsp, %rbp");
        let size = (self.frame.words * 8).div_ceil(16) * 16;
        if size >= 4096 {
            // Touch every allocated page so a large frame cannot jump over the
            // operating system's guard page. r11 is volatile on both target ABIs.
            let probe = self.label("stack_probe");
            self.emit(format!("    movq ${}, %r11", size / 4096));
            self.emit(format!("{probe}:"));
            self.emit("    subq $4096, %rsp");
            self.emit("    orq $0, (%rsp)");
            self.emit("    decq %r11");
            self.emit(format!("    jne {probe}"));
            if !size.is_multiple_of(4096) {
                self.emit(format!("    subq ${}, %rsp", size % 4096));
            }
        } else if size != 0 {
            self.emit(format!("    subq ${size}, %rsp"));
        }
        let registers = self.registers();
        let hidden = usize::from(self.frame.result_pointer.is_some());
        if let Some(offset) = self.frame.result_pointer {
            self.emit(format!("    movq {}, -{offset}(%rbp)", registers[0]));
        }
        // Preserve every raw incoming value before aggregate copies use volatile
        // argument registers. Each array local has room to hold its raw pointer.
        for index in 0..function.params.len() {
            let machine_index = index + hidden;
            let local_offset = self.frame.locals[index];
            if machine_index < registers.len() {
                self.emit(format!(
                    "    movq {}, -{}(%rbp)",
                    registers[machine_index], local_offset
                ));
            } else {
                let offset = if self.target == Target::Windows {
                    48
                } else {
                    16
                } + (machine_index - registers.len()) * 8;
                self.emit(format!("    movq {offset}(%rbp), %rax"));
                self.emit(format!("    movq %rax, -{local_offset}(%rbp)"));
            }
        }
        for (index, typ) in function.params.iter().enumerate() {
            if typ.aggregate() {
                let words = typ.words();
                let offset = self.frame.locals[index];
                self.emit(format!("    movq -{offset}(%rbp), %rax"));
                self.emit(format!("    leaq -{offset}(%rbp), %r10"));
                self.copy_array(words);
            }
        }
        self.block(&function.body);
        debug_assert_eq!(self.depth, 0);
        // Semantic analysis guarantees a return on all reachable paths.
        self.emit("    ud2");
        self.emit(format!("{}:", self.return_label));
        self.emit("    leave");
        self.emit("    ret");
    }
}

/// Historical value-only reference emitter. Owned buffers require `generate_checked`.
pub fn generate_reference(program: &IrProgram, target: Target) -> String {
    assert!(
        program.functions.iter().all(|f| f
            .locals
            .iter()
            .chain(&f.params)
            .chain(std::iter::once(&f.returns))
            .all(|t| *t != Type::Buffer)),
        "owned buffers require the verified CFG backend"
    );
    let mut generator = Generator {
        target,
        lines: vec![".text".into()],
        strings: BTreeMap::new(),
        label_counter: 0,
        depth: 0,
        return_label: String::new(),
        frame: Frame::default(),
        records: &program.records,
    };
    generator.emit(".globl main");
    generator.emit("main:");
    generator.emit("    pushq %rbp");
    generator.emit("    movq %rsp, %rbp");
    generator.call(&format!("v_fn_{}", program.main), 0, false);
    // Portable process status: Vela main's numeric result contributes low 8 bits.
    generator.emit("    andl $255, %eax");
    generator.emit("    leave");
    generator.emit("    ret");
    for (index, function) in program.functions.iter().enumerate() {
        generator.function(index, function);
    }
    generator.emit(".Lvela_runtime_fault:");
    // Faults may occur with arbitrary expression temporaries on the stack. rbp
    // restores a known alignment before calling the runtime and never returns.
    generator.emit("    movq %rbp, %rsp");
    generator.depth = 0;
    generator.emit("    leaq .Lvela_fault_message(%rip), %rax");
    generator.push();
    generator.call("puts", 1, false);
    generator.emit("    movq $70, %rax");
    generator.push();
    generator.call("exit", 1, false);
    generator.emit("    ud2");
    generator.emit(".Lvela_bounds_fault:");
    generator.emit("    movq %rbp, %rsp");
    generator.depth = 0;
    generator.emit("    leaq .Lvela_bounds_message(%rip), %rax");
    generator.push();
    generator.call("puts", 1, false);
    generator.emit("    movq $71, %rax");
    generator.push();
    generator.call("exit", 1, false);
    generator.emit("    ud2");
    generator.emit(if target == Target::Windows {
        ".section .rdata"
    } else {
        ".section .rodata"
    });
    generator.emit(format!(
        ".Lvela_fmt_num: .asciz \"{}\\n\"",
        if target == Target::Windows {
            "%lld"
        } else {
            "%ld"
        }
    ));
    generator.emit(".Lvela_true: .asciz \"true\"");
    generator.emit(".Lvela_false: .asciz \"false\"");
    generator.emit(
        ".Lvela_fault_message: .asciz \"vela runtime error: integer overflow or invalid division\"",
    );
    generator
        .emit(".Lvela_bounds_message: .asciz \"vela runtime error: array index out of bounds\"");
    for (value, label) in &generator.strings {
        let bytes: Vec<String> = value
            .as_bytes()
            .iter()
            .chain(std::iter::once(&0))
            .map(u8::to_string)
            .collect();
        generator
            .lines
            .push(format!("{label}: .byte {}", bytes.join(", ")));
    }
    if target == Target::Linux {
        generator.emit(".section .note.GNU-stack,\"\",@progbits");
    }
    generator.lines.push(String::new());
    generator.lines.join("\n")
}

/// Compile checked structured IR through the machine CFG and storage planner.
pub fn generate_checked(
    program: &IrProgram,
    target: Target,
    release: bool,
) -> Result<String, String> {
    let prepared = crate::cfg::prepare(program, release)?;
    Ok(crate::cfg_codegen::emit(&prepared, target))
}

/// Convenience API for callers that already enforce compiler invariants.
/// Source-facing clients should use `generate_checked` for resource diagnostics.
pub fn generate(program: &IrProgram, target: Target) -> String {
    generate_checked(program, target, false).expect("checked IR must lower to valid native CFG")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn literal(number: i64) -> IrExpr {
        IrExpr {
            kind: IrExprKind::Literal(Literal::Num(number)),
            typ: Type::Num,
            span: Span::default(),
        }
    }

    fn program(body: Vec<IrStmt>) -> IrProgram {
        IrProgram {
            main: 0,
            records: vec![],
            functions: vec![
                IrFunction {
                    name: "main".into(),
                    params: vec![],
                    returns: Type::Num,
                    locals: vec![],
                    body,
                },
                IrFunction {
                    name: "callee".into(),
                    params: vec![Type::Num; 6],
                    returns: Type::Num,
                    locals: vec![Type::Num; 6],
                    body: vec![IrStmt::Return(IrExpr {
                        kind: IrExprKind::Local(0),
                        typ: Type::Num,
                        span: Span::default(),
                    })],
                },
            ],
        }
    }

    #[test]
    fn windows_six_arguments_use_shadow_space_and_stack_slots() {
        let call = IrExpr {
            kind: IrExprKind::Call(1, (1..=6).map(literal).collect()),
            typ: Type::Num,
            span: Span::default(),
        };
        let assembly = generate(&program(vec![IrStmt::Return(call)]), Target::Windows);
        assert!(assembly.contains("movq %r11, 32(%rsp)"));
        assert!(assembly.contains("movq %r11, 40(%rsp)"));
        assert!(assembly.contains("movq 88(%rsp), %rcx"));
        assert!(assembly.contains("addq $96, %rsp"));
    }

    #[test]
    fn linux_uses_six_registers_and_nonexecutable_stack() {
        let call = IrExpr {
            kind: IrExprKind::Call(1, (1..=6).map(literal).collect()),
            typ: Type::Num,
            span: Span::default(),
        };
        let assembly = generate(&program(vec![IrStmt::Return(call)]), Target::Linux);
        assert!(assembly.contains("movq 40(%rsp), %rdi"));
        assert!(assembly.contains("movq 0(%rsp), %r9"));
        assert!(assembly.contains(".note.GNU-stack"));
        assert!(!assembly.contains(".section .rdata"));
    }

    #[test]
    fn arithmetic_checks_overflow_and_division_faults() {
        let value = IrExpr {
            kind: IrExprKind::Binary(
                Binary::Div,
                Box::new(literal(i64::MIN)),
                Box::new(literal(-1)),
            ),
            typ: Type::Num,
            span: Span::default(),
        };
        let assembly = generate(&program(vec![IrStmt::Return(value)]), Target::Linux);
        assert!(assembly.contains("movabsq $-9223372036854775808, %r11"));
        assert!(assembly.contains("je .Lvela_runtime_fault"));
        assert!(assembly.contains("movq $70, %rax"));
    }
}
