//! Typed machine-oriented control flow, effects and storage planning.
use crate::model::{Binary, IrProgram, IrRecord, Literal, Type, Unary};
use std::collections::BTreeSet;

mod analysis;
mod lower;
mod verify;
pub use analysis::{allocate, analyze, optimize};
pub use lower::lower;
pub use verify::verify;

pub type ValueId = usize;
pub type BlockId = usize;
pub type ValueSet = BTreeSet<ValueId>;
pub const MAX_CFG_BLOCKS: usize = 65536;
pub const MAX_CFG_VALUES: usize = 262144;

#[derive(Clone, Debug)]
pub struct Program {
    pub functions: Vec<Function>,
    pub records: Vec<IrRecord>,
    pub main: usize,
}
#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub params: Vec<Type>,
    pub returns: Type,
    pub locals: Vec<Type>,
    pub values: Vec<Type>,
    pub blocks: Vec<Block>,
    pub entry: BlockId,
}
#[derive(Clone, Debug)]
pub struct Block {
    pub instructions: Vec<Instruction>,
    pub terminator: Terminator,
}
#[derive(Clone, Debug)]
pub enum Terminator {
    Jump(BlockId),
    Branch {
        condition: ValueId,
        yes: BlockId,
        no: BlockId,
    },
    Return(ValueId),
    Unreachable,
}
#[derive(Clone, Debug)]
pub enum Projection {
    Field(usize),
    Index(ValueId),
}
#[derive(Clone, Debug)]
pub struct Place {
    pub slot: usize,
    pub projections: Vec<Projection>,
}
#[derive(Clone, Debug)]
pub enum Rvalue {
    Literal(Literal),
    Use(ValueId),
    LoadLocal(usize),
    /// Transfer a buffer out of its local and clear the local's runtime owner.
    TakeLocal(usize),
    Buffer(ValueId),
    BufferCopy(usize),
    BufferLen(usize),
    BufferGet {
        slot: usize,
        index: ValueId,
    },
    Unary(Unary, ValueId),
    Binary(Binary, ValueId, ValueId),
    Call(usize, Vec<ValueId>),
    Array(Vec<ValueId>),
    ArrayRepeat(ValueId, usize),
    Index {
        base: ValueId,
        index: ValueId,
    },
    Len(ValueId),
    Record {
        record: usize,
        fields: Vec<(usize, ValueId)>,
    },
    Field {
        base: ValueId,
        field: usize,
    },
    ReadPlace(Place),
}
#[derive(Clone, Debug)]
pub enum Instruction {
    Define {
        value: ValueId,
        rvalue: Rvalue,
    },
    StoreLocal {
        slot: usize,
        value: ValueId,
    },
    StorePlace {
        place: Place,
        value: ValueId,
    },
    Say(ValueId),
    CheckIndex {
        index: ValueId,
        length: usize,
    },
    DropLocal(usize),
    CheckBufferIndex {
        slot: usize,
        index: ValueId,
    },
    BufferStore {
        slot: usize,
        index: ValueId,
        value: ValueId,
    },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Effect {
    Pure,
    ReadLocal,
    WriteLocal,
    Checked,
    Output,
    Call,
}
impl Instruction {
    pub fn effect(&self) -> Effect {
        match self {
            Self::Define { rvalue, .. } => match rvalue {
                Rvalue::Call(..) | Rvalue::Buffer(_) | Rvalue::BufferCopy(_) => Effect::Call,
                // A move must survive DCE even when the new owner is unused.
                Rvalue::TakeLocal(_) => Effect::WriteLocal,
                Rvalue::Unary(Unary::Neg, _)
                | Rvalue::Binary(
                    Binary::Add | Binary::Sub | Binary::Mul | Binary::Div | Binary::Rem,
                    _,
                    _,
                ) => Effect::Checked,
                Rvalue::LoadLocal(_)
                | Rvalue::ReadPlace(_)
                | Rvalue::BufferLen(_)
                | Rvalue::BufferGet { .. } => Effect::ReadLocal,
                _ => Effect::Pure,
            },
            Self::StoreLocal { .. } | Self::StorePlace { .. } | Self::BufferStore { .. } => {
                Effect::WriteLocal
            }
            Self::Say(_) => Effect::Output,
            Self::CheckIndex { .. } | Self::CheckBufferIndex { .. } => Effect::Checked,
            Self::DropLocal(_) => Effect::Call,
        }
    }
    pub fn defined(&self) -> Option<ValueId> {
        match self {
            Self::Define { value, .. } => Some(*value),
            _ => None,
        }
    }
    pub fn used(&self) -> Vec<ValueId> {
        fn place(place: &Place) -> Vec<ValueId> {
            place
                .projections
                .iter()
                .filter_map(|p| match p {
                    Projection::Index(v) => Some(*v),
                    _ => None,
                })
                .collect()
        }
        match self {
            Self::Define { rvalue, .. } => match rvalue {
                Rvalue::Literal(_)
                | Rvalue::LoadLocal(_)
                | Rvalue::TakeLocal(_)
                | Rvalue::BufferCopy(_)
                | Rvalue::BufferLen(_) => vec![],
                Rvalue::Buffer(v) | Rvalue::BufferGet { index: v, .. } => vec![*v],
                Rvalue::Use(v)
                | Rvalue::Unary(_, v)
                | Rvalue::ArrayRepeat(v, _)
                | Rvalue::Len(v)
                | Rvalue::Field { base: v, .. } => vec![*v],
                Rvalue::Binary(_, a, b) | Rvalue::Index { base: a, index: b } => vec![*a, *b],
                Rvalue::Call(_, args) | Rvalue::Array(args) => args.clone(),
                Rvalue::Record { fields, .. } => fields.iter().map(|(_, v)| *v).collect(),
                Rvalue::ReadPlace(p) => place(p),
            },
            Self::StoreLocal { value, .. } | Self::Say(value) => vec![*value],
            Self::StorePlace { place: p, value } => {
                let mut used = place(p);
                used.push(*value);
                used
            }
            Self::CheckIndex { index, .. } | Self::CheckBufferIndex { index, .. } => vec![*index],
            Self::DropLocal(_) => vec![],
            Self::BufferStore { index, value, .. } => vec![*index, *value],
        }
    }
}
impl Terminator {
    pub fn successors(&self) -> Vec<BlockId> {
        match self {
            Self::Jump(b) => vec![*b],
            Self::Branch { yes, no, .. } => {
                if yes == no {
                    vec![*yes]
                } else {
                    vec![*yes, *no]
                }
            }
            _ => vec![],
        }
    }
    pub fn used(&self) -> Vec<ValueId> {
        match self {
            Self::Branch { condition, .. } | Self::Return(condition) => vec![*condition],
            _ => vec![],
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Register {
    R8,
    R9,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Location {
    Register(Register),
    Stack { offset: usize },
}
#[derive(Clone, Debug)]
pub struct Allocation {
    /// End offsets in bytes below rbp; an aggregate's element zero is at -offset.
    pub locals: Vec<usize>,
    pub values: Vec<Location>,
    pub result_pointer: Option<usize>,
    pub words: usize,
}
#[derive(Clone, Debug)]
pub struct Analysis {
    pub live_in: Vec<ValueSet>,
    pub live_out: Vec<ValueSet>,
    pub live_after: Vec<Vec<ValueSet>>,
    pub cross_call: ValueSet,
}
#[derive(Clone, Debug)]
pub struct PreparedProgram {
    program: Program,
    allocations: Vec<Allocation>,
}
impl PreparedProgram {
    pub fn program(&self) -> &Program {
        &self.program
    }
    pub fn allocations(&self) -> &[Allocation] {
        &self.allocations
    }
}
/// The only constructor for a checked program with matching storage plans.
pub fn prepare(source: &IrProgram, release: bool) -> Result<PreparedProgram, String> {
    crate::ir::verify(source)?;
    let mut program = lower(source);
    verify(&program)?;
    if release {
        optimize(&mut program);
        verify(&program)?;
    }
    let allocations = program
        .functions
        .iter()
        .map(allocate)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(PreparedProgram {
        program,
        allocations,
    })
}
