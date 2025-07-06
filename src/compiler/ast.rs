enum Type {
    Field,
    U32,
    Bool,
    Array(Box<Type>, u32),
    Ref(Box<Type>),
    Unit,
}

type Ident = String;

pub struct Expr<A> {
    shape: ExprS<A>,
    data: A,
}

pub enum ExprS<A> {
    LetIn(Ident, Box<Expr<A>>, Box<Expr<A>>),
    Alloc(Type),
    WriteRef(Box<Expr<A>>, Box<Expr<A>>),
    ReadRef(Box<Expr<A>>),
    Ident(Ident),
    Seq(Box<Expr<A>>, Box<Expr<A>>),
    Ite(Box<Expr<A>>, Box<Expr<A>>, Box<Expr<A>>),
    For(Ident, Box<Expr<A>>, Box<Expr<A>>),
    ArrayRead(Box<Expr<A>>, Box<Expr<A>>),
    Call(String, Vec<Box<Expr<A>>>),
    Nop,
}

