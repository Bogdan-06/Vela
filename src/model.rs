//! Shared source, AST and typed structured IR contracts.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Span {
    pub line: usize,
    pub column: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub span: Span,
    pub message: String,
    /// Additional diagnostic locations in the same source file.
    pub related: Vec<(Span, String)>,
}
impl Diagnostic {
    pub fn new(span: Span, message: impl Into<String>) -> Self {
        Self {
            span,
            message: message.into(),
            related: Vec::new(),
        }
    }
    pub fn with_related(mut self, span: Span, message: impl Into<String>) -> Self {
        self.related.push((span, message.into()));
        self
    }
    pub fn render(&self, path: &str, source: &str) -> String {
        let line = source
            .lines()
            .nth(self.span.line.saturating_sub(1))
            .unwrap_or("");
        let mut rendered = format!(
            "{}:{}:{}: error: {}\n  {}\n  {}^",
            path,
            self.span.line,
            self.span.column,
            self.message,
            line,
            " ".repeat(self.span.column.saturating_sub(1))
        );
        for (span, message) in &self.related {
            rendered.push_str(&format!(
                "\n{}:{}:{}: note: {}",
                path, span.line, span.column, message
            ));
        }
        rendered
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScalarType {
    Num,
    Flag,
    Text,
}
impl ScalarType {
    pub fn typ(self) -> Type {
        match self {
            Self::Num => Type::Num,
            Self::Flag => Type::Flag,
            Self::Text => Type::Text,
        }
    }
}
pub const MAX_ARRAY_LEN: usize = 4096;
/// Maximum allocated native fixed-frame words, after temporary storage reuse.
pub const MAX_FRAME_WORDS: usize = 65536;
pub const MAX_RECORD_FIELDS: usize = 128;
pub const MAX_RECORD_TYPES: usize = 1024;
pub const MAX_RECORD_DEPTH: usize = 64;
pub const MAX_RECORD_WORDS: usize = 16384;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Type {
    Num,
    Flag,
    Text,
    /// Affine numeric buffer owner; a single opaque native pointer.
    Buffer,
    Array(ScalarType, usize),
    /// Canonical record id plus verified cached layout width in eight-byte words.
    Record {
        id: usize,
        words: usize,
    },
}
impl Type {
    pub fn scalar(self) -> Option<ScalarType> {
        match self {
            Self::Num => Some(ScalarType::Num),
            Self::Flag => Some(ScalarType::Flag),
            Self::Text => Some(ScalarType::Text),
            Self::Buffer | Self::Array(..) | Self::Record { .. } => None,
        }
    }
    pub fn words(self) -> usize {
        match self {
            Self::Array(_, len) => len,
            Self::Record { words, .. } => words,
            _ => 1,
        }
    }
    pub fn aggregate(self) -> bool {
        matches!(self, Self::Array(..) | Self::Record { .. })
    }
}
impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Num => write!(f, "num"),
            Self::Flag => write!(f, "flag"),
            Self::Text => write!(f, "text"),
            Self::Buffer => write!(f, "buffer"),
            Self::Array(element, len) => write!(f, "[{}; {}]", element.typ(), len),
            Self::Record { id, .. } => write!(f, "record#{id}"),
        }
    }
}
#[derive(Clone, Debug)]
pub enum TypeSyntax {
    Resolved(Type),
    Named(String),
}
impl From<Type> for TypeSyntax {
    fn from(typ: Type) -> Self {
        Self::Resolved(typ)
    }
}
#[derive(Clone, Debug)]
pub struct FieldDecl {
    pub name: String,
    pub typ: TypeSyntax,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub struct RecordDecl {
    pub name: String,
    pub fields: Vec<FieldDecl>,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub struct FieldValue {
    pub name: String,
    pub value: Expr,
    pub span: Span,
}
#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    Num(i64),
    Flag(bool),
    Text(String),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Unary {
    Neg,
    Not,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Binary {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}
#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub enum ExprKind {
    Literal(Literal),
    Var(String),
    Unary(Unary, Box<Expr>),
    Binary(Binary, Box<Expr>, Box<Expr>),
    Call(String, Vec<Expr>),
    Array(Vec<Expr>),
    ArrayRepeat(Box<Expr>, usize),
    Index(Box<Expr>, Box<Expr>),
    Len(Box<Expr>),
    Buffer(Box<Expr>),
    BufferCopy(Box<Expr>),
    Record {
        name: String,
        fields: Vec<FieldValue>,
    },
    Field {
        base: Box<Expr>,
        name: String,
    },
}
#[derive(Clone, Debug)]
pub enum Projection {
    Field { name: String, span: Span },
    Index(Expr),
}
#[derive(Clone, Debug)]
pub struct Place {
    pub name: String,
    pub projections: Vec<Projection>,
}
#[derive(Clone, Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub enum StmtKind {
    Let {
        name: String,
        mutable: bool,
        value: Expr,
    },
    Assign {
        place: Place,
        value: Expr,
    },
    Say(Expr),
    Return(Expr),
    If {
        condition: Expr,
        yes: Vec<Stmt>,
        no: Vec<Stmt>,
    },
    While {
        condition: Expr,
        body: Vec<Stmt>,
    },
}
#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub typ: TypeSyntax,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub params: Vec<Param>,
    pub returns: TypeSyntax,
    pub body: Vec<Stmt>,
    pub span: Span,
}
#[derive(Clone, Debug, Default)]
pub struct Program {
    pub functions: Vec<Function>,
    pub records: Vec<RecordDecl>,
}
#[derive(Clone, Debug)]
pub struct IrExpr {
    pub kind: IrExprKind,
    pub typ: Type,
    pub span: Span,
}
#[derive(Clone, Debug)]
pub enum IrExprKind {
    Literal(Literal),
    Local(usize),
    Unary(Unary, Box<IrExpr>),
    Binary(Binary, Box<IrExpr>, Box<IrExpr>),
    Call(usize, Vec<IrExpr>),
    Array(Vec<IrExpr>),
    ArrayRepeat(Box<IrExpr>, usize),
    Index(Box<IrExpr>, Box<IrExpr>),
    Len(Box<IrExpr>),
    Buffer(Box<IrExpr>),
    BufferCopy {
        slot: usize,
    },
    BufferLen {
        slot: usize,
    },
    BufferGet {
        slot: usize,
        index: Box<IrExpr>,
    },
    Record {
        record: usize,
        fields: Vec<(usize, IrExpr)>,
    },
    Field {
        base: Box<IrExpr>,
        field: usize,
    },
}
#[derive(Clone, Debug)]
pub enum IrProjection {
    Field(usize),
    Index(IrExpr),
}
#[derive(Clone, Debug)]
pub struct IrPlace {
    pub slot: usize,
    pub projections: Vec<IrProjection>,
}
#[derive(Clone, Debug)]
pub enum IrStmt {
    Store(usize, IrExpr),
    /// Nullable cleanup of an owning local, including a moved-from local.
    Drop(usize),
    BufferStore {
        slot: usize,
        index: IrExpr,
        value: IrExpr,
    },
    StorePlace {
        place: IrPlace,
        value: IrExpr,
    },
    Say(IrExpr),
    Return(IrExpr),
    If {
        condition: IrExpr,
        yes: Vec<IrStmt>,
        no: Vec<IrStmt>,
    },
    While {
        condition: IrExpr,
        body: Vec<IrStmt>,
    },
}
#[derive(Clone, Debug)]
pub struct IrFunction {
    pub name: String,
    pub params: Vec<Type>,
    pub returns: Type,
    pub locals: Vec<Type>,
    pub body: Vec<IrStmt>,
}
#[derive(Clone, Debug)]
pub struct IrProgram {
    pub functions: Vec<IrFunction>,
    pub records: Vec<IrRecord>,
    pub main: usize,
}
#[derive(Clone, Debug)]
pub struct IrField {
    pub name: String,
    pub typ: Type,
    pub offset: usize,
}
#[derive(Clone, Debug)]
pub struct IrRecord {
    pub name: String,
    pub fields: Vec<IrField>,
    pub words: usize,
}
