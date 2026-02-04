/// AST for the Solo dialect under the ephapax-linear toolchain.
#[derive(Debug, Clone)]
pub enum Affinity {
    Linear,
    Affine,
    Unlimited,
}

#[derive(Debug, Clone)]
pub enum UnaryOp {
    Negate,
    Not,
}

#[derive(Debug, Clone)]
pub enum BinaryOp {
    Assign,
    Add,
    Sub,
    Multiply,
    Divide,
    Equal,
    NotEqual,
    Lt,
    Gt,
    Lte,
    Gte,
    And,
    Or,
    Range,
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64),
    Bool(bool),
    Str(String),
}

#[derive(Debug, Clone)]
pub enum Expr {
    Literal(Literal),
    Ident(String),
    Unary(UnaryOp, Box<Expr>),
    Binary(Box<Expr>, BinaryOp, Box<Expr>),
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
    Assign {
        name: String,
        expr: Box<Expr>,
    },
    FieldAccess {
        target: Box<Expr>,
        field: String,
    },
    Index {
        target: Box<Expr>,
        index: Box<Expr>,
    },
    Array(Vec<Expr>),
    Record(Vec<(String, Expr)>),
    Tuple(Vec<Expr>),
    Block(Vec<Statement>),
    Range(Box<Expr>, Box<Expr>),
    Restrict(Box<Expr>),
    Try {
        expr: Box<Expr>,
        propagate: bool,
    },
}

#[derive(Debug, Clone)]
pub enum Statement {
    Expr(Expr),
    Let {
        name: String,
        expr: Expr,
        affinity: Affinity,
    },
    Destructure {
        names: Vec<String>,
        expr: Expr,
    },
    Return(Option<Expr>),
    If {
        cond: Expr,
        then_branch: Vec<Statement>,
        else_branch: Option<Vec<Statement>>,
    },
    While {
        cond: Expr,
        body: Vec<Statement>,
    },
    For {
        var: String,
        iterable: Expr,
        body: Vec<Statement>,
    },
    Go(Vec<Statement>),
    Await(Expr),
    Try {
        expr: Expr,
        propagate: bool,
    },
    Comptime(Vec<Statement>),
    Block(Vec<Statement>),
}

#[derive(Debug, Clone)]
pub enum Item {
    Function(Function),
    Struct(StructDecl),
    Effect(EffectDecl),
    EffectImpl(EffectImpl),
    Import(ImportDecl),
    Arena(ArenaDecl),
    Comptime(Vec<Statement>),
}

#[derive(Debug, Clone)]
pub struct Module {
    pub items: Vec<Item>,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: String,
    pub affinity: Affinity,
    pub ty: TypeExpr,
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: String,
    pub modifiers: Vec<FnModifier>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub contract: Vec<ContractClause>,
    pub body: Vec<Statement>,
    pub is_public: bool,
}

#[derive(Debug, Clone)]
pub enum FnModifier {
    Async,
    Safe,
}

#[derive(Debug, Clone)]
pub enum TypeExpr {
    Named(String),
    Reference {
        mutable: bool,
        target: Box<TypeExpr>,
    },
    Array(Box<TypeExpr>),
    Record(Vec<(String, TypeExpr)>),
    Function {
        params: Vec<TypeExpr>,
        return_type: Box<TypeExpr>,
    },
    Effect(Box<TypeExpr>),
    Tuple(Vec<TypeExpr>),
    Unit,
}

#[derive(Debug, Clone)]
pub struct ContractClause {
    pub kind: ContractKind,
    pub condition: Expr,
}

#[derive(Debug, Clone)]
pub enum ContractKind {
    Pre,
    Post,
    Invariant,
}

#[derive(Debug, Clone)]
pub struct StructDecl {
    pub name: String,
    pub fields: Vec<StructField>,
    pub is_public: bool,
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub name: String,
    pub ty: TypeExpr,
}

#[derive(Debug, Clone)]
pub struct EffectDecl {
    pub name: String,
    pub ops: Vec<EffectOp>,
    pub is_public: bool,
}

#[derive(Debug, Clone)]
pub struct EffectOp {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
}

#[derive(Debug, Clone)]
pub struct EffectImpl {
    pub effect: String,
    pub handlers: Vec<EffectHandler>,
}

#[derive(Debug, Clone)]
pub struct EffectHandler {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub body: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub struct ImportDecl {
    pub path: Vec<String>,
    pub clause: Option<ImportClause>,
    pub is_public: bool,
}

#[derive(Debug, Clone)]
pub enum ImportClause {
    Glob,
    Items(Vec<String>),
}

#[derive(Debug, Clone)]
pub struct ArenaDecl {
    pub name: String,
}
