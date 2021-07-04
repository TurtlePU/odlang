pub type Program = Vec<Decl>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Name(pub String);

impl<'a> From<&'a str> for Name {
    fn from(x: &'a str) -> Self {
        Self(x.into())
    }
}

#[derive(Debug)]
pub struct Binding {
    pub name: Name,
    pub expr: Expr,
}

#[derive(Debug)]
pub struct CompTime {
    pub name: Name,
    pub typevars: Vec<String>,
    pub body: Body,
}

#[derive(Debug)]
pub enum Decl {
    TopLevelValue(Binding),
    CompTime(CompTime),
}

#[derive(Debug)]
pub struct Expr {
    pub expr_type: Type,
    pub expr_value: Value
}

#[derive(Debug)]
pub enum Tuple<T> {
    Mult(Vec<T>),
    Add(Vec<T>),
}

#[derive(Debug)]
pub enum Type {
    Hole(String),
    Nominal(Name),
    Tuple(Tuple<Type>),
    Arrow {
        from: Box<Type>,
        to: Box<Type>,
        effects: Vec<Type>,
    },
}

#[derive(Debug)]
pub enum Value {
    Variable(Name),
    Tuple(Tuple<Expr>),
    Function(Function),
    Call(Call),
    Block(Vec<Stmt>),
}

#[derive(Debug)]
pub enum Stmt {
    Expression(Expr),
    Binding(Binding),
}

#[derive(Debug)]
pub struct Function(pub Vec<Branch>);

#[derive(Debug)]
pub struct Call {
    pub function: Box<Expr>,
    pub args: Vec<Expr>,
}

#[derive(Debug)]
pub struct Branch {
    pub pattern: Pattern,
    pub expression: Expr,
    pub effects: Vec<Type>,
}

pub type Pattern = Expr;

#[derive(Debug)]
pub enum Body {
    Data {
        variants: Vec<Variant>,
    },
    Effect {
        variants: Vec<Variant>,
        value: Option<Type>,
    },
}

#[derive(Debug)]
pub struct Variant {
    pub name: Name,
    pub tuple: Tuple<Type>,
}
