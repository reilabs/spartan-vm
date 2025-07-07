use crate::compiler::ssa::{Type, ValueId};

pub struct Expr<A> {
    shape: ExprS<A>,
    data: A,
}

pub enum ExprS<A> {
    LetIn(ValueId, Box<Expr<A>>, Box<Expr<A>>),
    Alloc(Type),
    WriteRef(Box<Expr<A>>, Box<Expr<A>>),
    ReadRef(Box<Expr<A>>),
    Ident(ValueId),
    Seq(Box<Expr<A>>, Box<Expr<A>>),
    Ite(Box<Expr<A>>, Box<Expr<A>>, Box<Expr<A>>),
    For(ValueId, Box<Expr<A>>, Box<Expr<A>>, Box<Expr<A>>),
    ArrayRead(Box<Expr<A>>, Box<Expr<A>>),
    Call(String, Vec<Box<Expr<A>>>),
    Nop,
    AssertEq(Box<Expr<A>>, Box<Expr<A>>),
}

impl<A> Expr<A> {
    pub fn let_in(ident: ValueId, expr: Expr<()>, body: Expr<()>) -> Expr<()> {
        Expr {
            shape: ExprS::LetIn(ident, Box::new(expr), Box::new(body)),
            data: (),
        }
    }

    pub fn alloc(ty: Type) -> Expr<()> {
        Expr {
            shape: ExprS::Alloc(ty),
            data: (),
        }
    }

    pub fn write_ref(ref_expr: Expr<()>, value_expr: Expr<()>) -> Expr<()> {
        Expr {
            shape: ExprS::WriteRef(Box::new(ref_expr), Box::new(value_expr)),
            data: (),
        }
    }

    pub fn read_ref(ref_expr: Expr<()>) -> Expr<()> {
        Expr {
            shape: ExprS::ReadRef(Box::new(ref_expr)),
            data: (),
        }
    }

    pub fn seq(expr1: Expr<()>, expr2: Expr<()>) -> Expr<()> {
        Expr {
            shape: ExprS::Seq(Box::new(expr1), Box::new(expr2)),
            data: (),
        }
    }

    pub fn ite(cond: Expr<()>, then: Expr<()>, otherwise: Expr<()>) -> Expr<()> {
        Expr {
            shape: ExprS::Ite(Box::new(cond), Box::new(then), Box::new(otherwise)),
            data: (),
        }
    }

    pub fn for_(ident: ValueId, lo: Expr<()>, hi: Expr<()>, body: Expr<()>) -> Expr<()> {
        Expr {
            shape: ExprS::For(ident, Box::new(lo), Box::new(hi), Box::new(body)),
            data: (),
        }
    }

    pub fn array_read(array_expr: Expr<()>, index_expr: Expr<()>) -> Expr<()> {
        Expr {
            shape: ExprS::ArrayRead(Box::new(array_expr), Box::new(index_expr)),
            data: (),
        }
    }

    pub fn call(name: String, args: Vec<Box<Expr<()>>>) -> Expr<()> {
        Expr {
            shape: ExprS::Call(name, args),
            data: (),
        }
    }

    pub fn nop() -> Expr<()> {
        Expr {
            shape: ExprS::Nop,
            data: (),
        }
    }

    pub fn assert_eq(left: Expr<()>, right: Expr<()>) -> Expr<()> {
        Expr {
            shape: ExprS::AssertEq(Box::new(left), Box::new(right)),
            data: (),
        }
    }
}

pub struct Function<A> {
    name: String,
    args: Vec<(ValueId, Type)>,
    body: Box<Expr<A>>,
}

pub struct Program<A> {
    functions: Vec<Function<A>>,
}
