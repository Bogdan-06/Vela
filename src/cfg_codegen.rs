//! Native x86-64 emission from a verified CFG and its liveness-based storage plan.
use crate::cfg::{
    self, Allocation, Instruction, Location, PreparedProgram, Register, Rvalue, Terminator, ValueId,
};
use crate::codegen::Target;
use crate::model::{Binary, Literal, Type, Unary};
use std::collections::BTreeMap;

struct Emitter<'a> {
    program: &'a cfg::Program,
    allocations: &'a [Allocation],
    target: Target,
    function: usize,
    lines: Vec<String>,
    strings: BTreeMap<String, String>,
    next_label: usize,
    depth: usize,
}

impl Emitter<'_> {
    fn emit(&mut self, line: impl Into<String>) {
        self.lines.push(line.into());
    }
    fn label(&mut self, prefix: &str) -> String {
        let result = format!(".Lvela_{prefix}_{}", self.next_label);
        self.next_label += 1;
        result
    }
    fn block_label(&self, block: usize) -> String {
        format!(".Lvela_cfg_{}_{}", self.function, block)
    }
    fn allocation(&self) -> &Allocation {
        &self.allocations[self.function]
    }
    fn typ(&self, value: ValueId) -> Type {
        self.program.functions[self.function].values[value]
    }
    fn register(register: Register) -> &'static str {
        match register {
            Register::R8 => "%r8",
            Register::R9 => "%r9",
        }
    }
    fn registers(&self) -> &'static [&'static str] {
        match self.target {
            Target::Windows => &["%rcx", "%rdx", "%r8", "%r9"],
            Target::Linux => &["%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"],
        }
    }
    fn offset(&self, value: ValueId) -> usize {
        match self.allocation().values[value] {
            Location::Stack { offset } => offset,
            Location::Register(_) => unreachable!("aggregate values require stack storage"),
        }
    }
    /// This helper changes only the explicitly requested destination register.
    fn load(&mut self, value: ValueId, destination: &str) {
        let location = self.allocation().values[value];
        if self.typ(value).aggregate() {
            let Location::Stack { offset } = location else {
                unreachable!("aggregate register allocation")
            };
            self.emit(format!("    leaq -{offset}(%rbp), {destination}"));
        } else {
            match location {
                Location::Register(register) => {
                    let source = Self::register(register);
                    if source != destination {
                        self.emit(format!("    movq {source}, {destination}"));
                    }
                }
                Location::Stack { offset } => {
                    self.emit(format!("    movq -{offset}(%rbp), {destination}"))
                }
            }
        }
    }
    fn save_scalar(&mut self, value: ValueId) {
        debug_assert!(!self.typ(value).aggregate());
        match self.allocation().values[value] {
            Location::Register(register) => {
                self.emit(format!("    movq %rax, {}", Self::register(register)))
            }
            Location::Stack { offset } => self.emit(format!("    movq %rax, -{offset}(%rbp)")),
        }
    }
    fn push(&mut self) {
        self.emit("    pushq %rax");
        self.depth += 1;
    }
    fn call(&mut self, name: &str, arguments: usize, variadic: bool) {
        let registers = self.registers();
        let shadow = if self.target == Target::Windows {
            32
        } else {
            0
        };
        let required = shadow + arguments.saturating_sub(registers.len()) * 8;
        let padding = (16 - (self.depth * 8 + required) % 16) % 16;
        let reserved = required + padding;
        if reserved != 0 {
            self.emit(format!("    subq ${reserved}, %rsp"));
        }
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
            self.emit("    xorl %eax, %eax");
        }
        self.emit(format!("    call {name}"));
        let released = reserved + arguments * 8;
        if released != 0 {
            self.emit(format!("    addq ${released}, %rsp"));
        }
        self.depth -= arguments;
    }
    /// Copy rax -> r10 using volatile scratch registers, preserving r8/r9 values.
    fn copy(&mut self, words: usize) {
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
    /// Allocate a zeroed numeric buffer whose requested length is in rax.
    /// The original length lives on the temporary stack across the C call.
    fn buffer_allocate(&mut self) {
        self.emit("    testq %rax, %rax");
        self.emit("    js .Lvela_allocation_fault");
        self.emit("    movabsq $1152921504606846974, %r11");
        self.emit("    cmpq %r11, %rax");
        self.emit("    ja .Lvela_allocation_fault");
        self.push();
        self.emit("    addq $1, %rax");
        self.push();
        self.emit("    movq $8, %rax");
        self.push();
        self.call("calloc", 2, false);
        self.emit("    testq %rax, %rax");
        self.emit("    je .Lvela_allocation_fault");
        self.emit("    popq %r10");
        self.depth -= 1;
        self.emit("    movq %r10, (%rax)");
    }
    fn drop_local(&mut self, slot: usize) {
        let offset = self.allocation().locals[slot];
        self.emit(format!("    movq -{offset}(%rbp), %rax"));
        self.emit(format!("    movq $0, -{offset}(%rbp)"));
        self.push();
        // C free(NULL) is defined, including after a move or a conditional drop.
        self.call("free", 1, false);
    }
    fn place_address(&mut self, place: &cfg::Place) -> Type {
        let mut offset = self.allocation().locals[place.slot];
        let mut typ = self.program.functions[self.function].locals[place.slot];
        let mut indices = Vec::new();
        for projection in &place.projections {
            match projection {
                cfg::Projection::Field(index) => {
                    let Type::Record { id, .. } = typ else {
                        unreachable!("verified record projection")
                    };
                    let field = &self.program.records[id].fields[*index];
                    offset -= field.offset * 8;
                    typ = field.typ;
                }
                cfg::Projection::Index(index) => {
                    let Type::Array(element, ..) = typ else {
                        unreachable!("verified scalar-array projection")
                    };
                    indices.push(*index);
                    typ = element.typ();
                }
            }
        }
        self.emit(format!("    leaq -{offset}(%rbp), %rax"));
        for index in indices {
            self.load(index, "%r11");
            self.emit("    leaq (%rax,%r11,8), %rax");
        }
        typ
    }
    fn binary(&mut self, operator: Binary, left: ValueId, right: ValueId) {
        self.load(left, "%rax");
        self.load(right, "%r10");
        match operator {
            Binary::Add | Binary::Sub | Binary::Mul => {
                let opcode = match operator {
                    Binary::Add => "addq",
                    Binary::Sub => "subq",
                    _ => "imulq",
                };
                self.emit(format!("    {opcode} %r10, %rax"));
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
                if operator == Binary::Rem {
                    self.emit("    movq %rdx, %rax");
                }
            }
            Binary::And => self.emit("    andq %r10, %rax"),
            Binary::Or => self.emit("    orq %r10, %rax"),
            Binary::Eq | Binary::Ne | Binary::Lt | Binary::Le | Binary::Gt | Binary::Ge => {
                self.emit("    cmpq %r10, %rax");
                let opcode = match operator {
                    Binary::Eq => "sete",
                    Binary::Ne => "setne",
                    Binary::Lt => "setl",
                    Binary::Le => "setle",
                    Binary::Gt => "setg",
                    Binary::Ge => "setge",
                    _ => unreachable!(),
                };
                self.emit(format!("    {opcode} %al"));
                self.emit("    movzbq %al, %rax");
            }
        }
    }
    fn define(&mut self, value: ValueId, rvalue: &Rvalue) {
        let typ = self.typ(value);
        match rvalue {
            Rvalue::Literal(Literal::Num(number)) => {
                self.emit(format!("    movabsq ${number}, %rax"))
            }
            Rvalue::Literal(Literal::Flag(flag)) => {
                self.emit(format!("    movq ${}, %rax", usize::from(*flag)))
            }
            Rvalue::Literal(Literal::Text(text)) => {
                let label = if let Some(label) = self.strings.get(text) {
                    label.clone()
                } else {
                    let label = self.label("text");
                    self.strings.insert(text.clone(), label.clone());
                    label
                };
                self.emit(format!("    leaq {label}(%rip), %rax"));
            }
            Rvalue::Use(source) => {
                self.load(*source, "%rax");
                if typ.aggregate() {
                    let offset = self.offset(value);
                    self.emit(format!("    leaq -{offset}(%rbp), %r10"));
                    self.copy(typ.words());
                }
            }
            Rvalue::LoadLocal(slot) => {
                let offset = self.allocation().locals[*slot];
                if typ.aggregate() {
                    self.emit(format!("    leaq -{offset}(%rbp), %rax"));
                    let dest = self.offset(value);
                    self.emit(format!("    leaq -{dest}(%rbp), %r10"));
                    self.copy(typ.words());
                } else {
                    self.emit(format!("    movq -{offset}(%rbp), %rax"));
                }
            }
            Rvalue::TakeLocal(slot) => {
                let offset = self.allocation().locals[*slot];
                self.emit(format!("    movq -{offset}(%rbp), %rax"));
                self.emit(format!("    movq $0, -{offset}(%rbp)"));
            }
            Rvalue::Buffer(length) => {
                self.load(*length, "%rax");
                self.buffer_allocate();
            }
            Rvalue::BufferCopy(slot) => {
                let offset = self.allocation().locals[*slot];
                self.emit(format!("    movq -{offset}(%rbp), %rax"));
                self.emit("    movq (%rax), %rax");
                self.buffer_allocate();
                // Reload the live owning local after calloc clobbers scratch
                // registers. Copy the header too; zero length still copies it.
                self.emit(format!("    movq -{offset}(%rbp), %r10"));
                self.emit("    movq (%r10), %rcx");
                self.emit("    incq %rcx");
                self.emit("    xorl %r11d, %r11d");
                let begin = self.label("buffer_copy");
                self.emit(format!("{begin}:"));
                self.emit("    movq (%r10,%r11,8), %rdx");
                self.emit("    movq %rdx, (%rax,%r11,8)");
                self.emit("    incq %r11");
                self.emit("    cmpq %rcx, %r11");
                self.emit(format!("    jb {begin}"));
            }
            Rvalue::BufferLen(slot) => {
                let offset = self.allocation().locals[*slot];
                self.emit(format!("    movq -{offset}(%rbp), %rax"));
                self.emit("    movq (%rax), %rax");
            }
            Rvalue::BufferGet { slot, index } => {
                let offset = self.allocation().locals[*slot];
                self.emit(format!("    movq -{offset}(%rbp), %rax"));
                self.load(*index, "%r11");
                self.emit("    movq 8(%rax,%r11,8), %rax");
            }
            Rvalue::Unary(operator, input) => {
                self.load(*input, "%rax");
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
            Rvalue::Binary(operator, left, right) => self.binary(*operator, *left, *right),
            Rvalue::Call(index, arguments) => {
                if typ.aggregate() {
                    let offset = self.offset(value);
                    self.emit(format!("    leaq -{offset}(%rbp), %rax"));
                    self.push();
                }
                // Freeze all input values on the argument stack before ABI
                // register loading can overwrite an allocated r8/r9 input.
                for argument in arguments {
                    self.load(*argument, "%rax");
                    self.push();
                }
                self.call(
                    &format!("v_fn_{index}"),
                    arguments.len() + usize::from(typ.aggregate()),
                    false,
                );
            }
            Rvalue::Array(elements) => {
                let offset = self.offset(value);
                for (index, element) in elements.iter().enumerate() {
                    self.load(*element, "%rax");
                    self.emit(format!("    movq %rax, -{}(%rbp)", offset - index * 8));
                }
                self.emit(format!("    leaq -{offset}(%rbp), %rax"));
            }
            Rvalue::ArrayRepeat(input, length) => {
                self.load(*input, "%rax");
                let offset = self.offset(value);
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
            Rvalue::Index { base, index } => {
                self.load(*base, "%rax");
                self.load(*index, "%r11");
                self.emit("    movq (%rax,%r11,8), %rax");
            }
            Rvalue::Len(base) => {
                let Type::Array(_, length) = self.typ(*base) else {
                    unreachable!("verified length")
                };
                self.emit(format!("    movq ${length}, %rax"));
            }
            Rvalue::Record { record, fields } => {
                let offset = self.offset(value);
                for (field, input) in fields {
                    let destination =
                        offset - self.program.records[*record].fields[*field].offset * 8;
                    self.load(*input, "%rax");
                    if self.typ(*input).aggregate() {
                        self.emit(format!("    leaq -{destination}(%rbp), %r10"));
                        self.copy(self.typ(*input).words());
                    } else {
                        self.emit(format!("    movq %rax, -{destination}(%rbp)"));
                    }
                }
                self.emit(format!("    leaq -{offset}(%rbp), %rax"));
            }
            Rvalue::Field { base, field } => {
                let Type::Record { id, .. } = self.typ(*base) else {
                    unreachable!("verified field")
                };
                let bytes = self.program.records[id].fields[*field].offset * 8;
                self.load(*base, "%rax");
                if bytes != 0 {
                    self.emit(format!("    addq ${bytes}, %rax"));
                }
                if typ.aggregate() {
                    let offset = self.offset(value);
                    self.emit(format!("    leaq -{offset}(%rbp), %r10"));
                    self.copy(typ.words());
                } else {
                    self.emit("    movq (%rax), %rax");
                }
            }
            Rvalue::ReadPlace(place) => {
                self.place_address(place);
                if typ.aggregate() {
                    let offset = self.offset(value);
                    self.emit(format!("    leaq -{offset}(%rbp), %r10"));
                    self.copy(typ.words());
                } else {
                    self.emit("    movq (%rax), %rax");
                }
            }
        }
        if !typ.aggregate() {
            self.save_scalar(value);
        }
    }
    fn say(&mut self, value: ValueId) {
        match self.typ(value) {
            Type::Num => {
                self.emit("    leaq .Lvela_fmt_num(%rip), %rax");
                self.push();
                self.load(value, "%rax");
                self.push();
                self.call("printf", 2, true);
            }
            Type::Text => {
                self.load(value, "%rax");
                self.push();
                self.call("puts", 1, false);
            }
            Type::Flag => {
                let done = self.label("flag_print");
                self.load(value, "%rax");
                self.emit("    testq %rax, %rax");
                self.emit("    leaq .Lvela_false(%rip), %rax");
                self.emit(format!("    je {done}"));
                self.emit("    leaq .Lvela_true(%rip), %rax");
                self.emit(format!("{done}:"));
                self.push();
                self.call("puts", 1, false);
            }
            _ => unreachable!("verified scalar output"),
        }
    }
    fn instruction(&mut self, instruction: &Instruction) {
        match instruction {
            Instruction::Define { value, rvalue } => self.define(*value, rvalue),
            Instruction::StoreLocal { slot, value } => {
                self.load(*value, "%rax");
                let offset = self.allocation().locals[*slot];
                if self.typ(*value) == Type::Buffer {
                    // Freeze the incoming owner before releasing the replaced
                    // one, even if its allocated register is volatile or dying.
                    self.push();
                    self.drop_local(*slot);
                    self.emit("    popq %rax");
                    self.depth -= 1;
                    self.emit(format!("    movq %rax, -{offset}(%rbp)"));
                } else if self.typ(*value).aggregate() {
                    self.emit(format!("    leaq -{offset}(%rbp), %r10"));
                    self.copy(self.typ(*value).words());
                } else {
                    self.emit(format!("    movq %rax, -{offset}(%rbp)"));
                }
            }
            Instruction::StorePlace { place, value } => {
                let typ = self.place_address(place);
                self.emit("    movq %rax, %r10");
                self.load(*value, "%rax");
                if typ.aggregate() {
                    self.copy(typ.words());
                } else {
                    self.emit("    movq %rax, (%r10)");
                }
            }
            Instruction::Say(value) => self.say(*value),
            Instruction::CheckIndex { index, length } => {
                self.load(*index, "%rax");
                self.emit(format!("    cmpq ${length}, %rax"));
                self.emit("    jae .Lvela_bounds_fault");
            }
            Instruction::DropLocal(slot) => self.drop_local(*slot),
            Instruction::CheckBufferIndex { slot, index } => {
                let offset = self.allocation().locals[*slot];
                self.emit(format!("    movq -{offset}(%rbp), %rax"));
                self.load(*index, "%r11");
                self.emit("    cmpq (%rax), %r11");
                self.emit("    jae .Lvela_bounds_fault");
            }
            Instruction::BufferStore { slot, index, value } => {
                let offset = self.allocation().locals[*slot];
                self.emit(format!("    movq -{offset}(%rbp), %r10"));
                self.load(*index, "%r11");
                self.load(*value, "%rax");
                self.emit("    movq %rax, 8(%r10,%r11,8)");
            }
        }
        debug_assert_eq!(self.depth, 0);
    }
    fn terminator(&mut self, terminator: &Terminator) {
        match terminator {
            Terminator::Jump(block) => self.emit(format!("    jmp {}", self.block_label(*block))),
            Terminator::Branch { condition, yes, no } => {
                self.load(*condition, "%rax");
                self.emit("    testq %rax, %rax");
                self.emit(format!("    jne {}", self.block_label(*yes)));
                self.emit(format!("    jmp {}", self.block_label(*no)));
            }
            Terminator::Return(value) => {
                self.load(*value, "%rax");
                if self.typ(*value).aggregate() {
                    let offset = self
                        .allocation()
                        .result_pointer
                        .expect("aggregate return pointer");
                    self.emit(format!("    movq -{offset}(%rbp), %r10"));
                    self.copy(self.typ(*value).words());
                }
                self.emit("    leave");
                self.emit("    ret");
            }
            Terminator::Unreachable => self.emit("    ud2"),
        }
    }
    fn emit_function(&mut self, index: usize) {
        self.function = index;
        self.depth = 0;
        self.emit(format!("v_fn_{index}:"));
        self.emit("    pushq %rbp");
        self.emit("    movq %rsp, %rbp");
        let size = (self.allocation().words * 8).div_ceil(16) * 16;
        if size >= 4096 {
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
        // Nullable storage supports cleanup on paths where a declaration was
        // skipped, and makes transferring/replacing owners exactly once safe.
        // These immediate stores do not clobber incoming argument registers.
        for slot in 0..self.program.functions[index].locals.len() {
            if self.program.functions[index].locals[slot] == Type::Buffer {
                let offset = self.allocation().locals[slot];
                self.emit(format!("    movq $0, -{offset}(%rbp)"));
            }
        }
        let hidden = usize::from(self.allocation().result_pointer.is_some());
        if let Some(offset) = self.allocation().result_pointer {
            self.emit(format!("    movq {}, -{offset}(%rbp)", registers[0]));
        }
        let params = self.program.functions[index].params.clone();
        for param in 0..params.len() {
            let machine = param + hidden;
            let local = self.allocation().locals[param];
            if machine < registers.len() {
                self.emit(format!("    movq {}, -{local}(%rbp)", registers[machine]));
            } else {
                let incoming = if self.target == Target::Windows {
                    48
                } else {
                    16
                } + (machine - registers.len()) * 8;
                self.emit(format!("    movq {incoming}(%rbp), %rax"));
                self.emit(format!("    movq %rax, -{local}(%rbp)"));
            }
        }
        for (param, typ) in params.iter().enumerate() {
            if typ.aggregate() {
                let offset = self.allocation().locals[param];
                self.emit(format!("    movq -{offset}(%rbp), %rax"));
                self.emit(format!("    leaq -{offset}(%rbp), %r10"));
                self.copy(typ.words());
            }
        }
        let entry = self.program.functions[index].entry;
        self.emit(format!("    jmp {}", self.block_label(entry)));
        for block in 0..self.program.functions[index].blocks.len() {
            self.emit(format!("{}:", self.block_label(block)));
            let instructions = self.program.functions[index].blocks[block]
                .instructions
                .clone();
            for instruction in &instructions {
                self.instruction(instruction);
            }
            let terminator = self.program.functions[index].blocks[block]
                .terminator
                .clone();
            self.terminator(&terminator);
        }
    }
    fn fault(&mut self, label: &str, message: &str, status: usize) {
        self.emit(format!("{label}:"));
        self.emit("    movq %rbp, %rsp");
        self.depth = 0;
        self.emit(format!("    leaq {message}(%rip), %rax"));
        self.push();
        self.call("puts", 1, false);
        self.emit(format!("    movq ${status}, %rax"));
        self.push();
        self.call("exit", 1, false);
        self.emit("    ud2");
    }
}

/// Emit exactly the checked graph and its matching, sealed allocation plans.
pub fn emit(prepared: &PreparedProgram, target: Target) -> String {
    let program = prepared.program();
    let mut emitter = Emitter {
        program,
        allocations: prepared.allocations(),
        target,
        function: 0,
        lines: vec![".text".into()],
        strings: BTreeMap::new(),
        next_label: 0,
        depth: 0,
    };
    emitter.emit(".globl main");
    emitter.emit("main:");
    emitter.emit("    pushq %rbp");
    emitter.emit("    movq %rsp, %rbp");
    emitter.call(&format!("v_fn_{}", program.main), 0, false);
    emitter.emit("    andl $255, %eax");
    emitter.emit("    leave");
    emitter.emit("    ret");
    for index in 0..program.functions.len() {
        emitter.emit_function(index);
    }
    emitter.fault(".Lvela_runtime_fault", ".Lvela_fault_message", 70);
    emitter.fault(".Lvela_bounds_fault", ".Lvela_bounds_message", 71);
    emitter.fault(".Lvela_allocation_fault", ".Lvela_allocation_message", 72);
    emitter.emit(if target == Target::Windows {
        ".section .rdata"
    } else {
        ".section .rodata"
    });
    emitter.emit(format!(
        ".Lvela_fmt_num: .asciz \"{}\\n\"",
        if target == Target::Windows {
            "%lld"
        } else {
            "%ld"
        }
    ));
    emitter.emit(".Lvela_true: .asciz \"true\"");
    emitter.emit(".Lvela_false: .asciz \"false\"");
    emitter.emit(
        ".Lvela_fault_message: .asciz \"vela runtime error: integer overflow or invalid division\"",
    );
    emitter.emit(".Lvela_bounds_message: .asciz \"vela runtime error: array index out of bounds\"");
    emitter.emit(".Lvela_allocation_message: .asciz \"vela runtime error: invalid buffer length or allocation failure\"");
    let strings = std::mem::take(&mut emitter.strings);
    for (value, label) in strings {
        let bytes = value
            .as_bytes()
            .iter()
            .chain(std::iter::once(&0))
            .map(u8::to_string)
            .collect::<Vec<_>>();
        emitter.emit(format!("{label}: .byte {}", bytes.join(", ")));
    }
    if target == Target::Linux {
        emitter.emit(".section .note.GNU-stack,\"\",@progbits");
    }
    emitter.lines.push(String::new());
    emitter.lines.join("\n")
}
