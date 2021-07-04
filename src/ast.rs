pub type Program<T, N> = Vec<Binding<T, N>>;

#[derive(Debug)]
pub struct Binding<T, N> {
    pub name: N,
    pub value: TLValue<T, N>,
}

#[derive(Debug)]
pub enum TLValue<T, N> {
    Expr(ValExpr<T, N>),
    Data(PureFun<TLParam<N>, Data<T, N>>),
}

#[derive(Debug)]
pub struct PureFun<F, T> {
    pub from: Vec<F>,
    pub to: T,
}

#[derive(Debug)]
pub enum TLParam<N> {
    TypeVar(N),
}

#[derive(Debug)]
pub struct GenExpr<T, V> {
    pub type_: T,
    pub value: V,
}

pub type ValExpr<T, N> = GenExpr<Type<T, N>, Value<T, N>>;

#[derive(Debug)]
pub enum Type<T, N> {
    Named(T),
    Apply(Apply<Type<T, N>>),
    Tuple(Tuple<Type<T, N>>),
    TypeFun(PureFun<TLParam<N>, Box<Type<T, N>>>),
    ValueFun {
        from: Tuple<Type<T, N>>,
        to: Box<Type<T, N>>,
        effects: Vec<Type<T, N>>,
    },
}

#[derive(Debug)]
pub struct Apply<T> {
    pub func: Box<T>,
    pub args: Vec<T>,
}

#[derive(Debug)]
pub struct Tuple<T> {
    pub kind: TupleKind,
    pub coords: Vec<T>,
}

#[derive(Debug)]
pub enum TupleKind {
    Multiplicative,
    Additive,
}

#[derive(Debug)]
pub enum Value<T, N> {
    Variable(N),
    Tuple(Tuple<ValExpr<T, N>>),
    Lambda(Vec<Branch<T, N>>),
    Apply(Apply<ValExpr<T, N>>),
    Block(Vec<Stmt<T, N>>),
}

#[derive(Debug)]
pub enum Stmt<T, N> {
    Just(ValExpr<T, N>),
    Raise(ValExpr<T, N>),
    Bind(Binding<T, N>),
}

#[derive(Debug)]
pub struct Branch<T, N>(pub PatExpr<T, N>, pub ValExpr<T, N>);

pub type PatExpr<T, N> = GenExpr<Type<T, N>, Pattern<T, N>>;

#[derive(Debug)]
pub enum Pattern<T, N> {
    Variable(N),
    Tuple(Tuple<PatExpr<T, N>>),
    Apply(Apply<PatExpr<T, N>>),
}

#[derive(Debug)]
pub struct Data<T, N> {
    pub variants: Vec<(Content<N>, Type<T, N>)>,
    pub effect: Option<Type<N, N>>,
}

#[derive(Debug)]
pub enum Content<N> {
    Variant(N, Tuple<Type<N, N>>),
    Other(Apply<Type<N, N>>),
}
