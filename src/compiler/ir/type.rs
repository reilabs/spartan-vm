use std::fmt::{Debug, Display, Formatter};

pub trait CommutativeSemigroup {
    fn empty() -> Self;
    fn op(&self, other: &Self) -> Self;
}

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct Empty;

impl CommutativeSemigroup for Empty {
    fn empty() -> Self {
        Empty
    }

    fn op(&self, other: &Self) -> Self {
        Empty
    }
}

impl Display for Empty {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "")
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeExpr<V> {
    Bool,
    Field,
    U32,
    Array(Box<Type<V>>, usize),
    Ref(Box<Type<V>>),
}

impl<V> TypeExpr<V> {
    pub fn equal_up_to_annotation(&self, other: &Self) -> bool {
        match (self, other) {
            (TypeExpr::Bool, TypeExpr::Bool) => true,
            (TypeExpr::Field, TypeExpr::Field) => true,
            (TypeExpr::U32, TypeExpr::U32) => true,
            (TypeExpr::Array(inner1, size1), TypeExpr::Array(inner2, size2)) => {
                inner1.equal_up_to_annotation(inner2) && size1 == size2
            }
            (TypeExpr::Ref(inner1), TypeExpr::Ref(inner2)) => inner1.equal_up_to_annotation(inner2),
            _ => false,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type<V> {
    pub expr: TypeExpr<V>,
    pub annotation: V,
}

impl<V: Display> Display for Type<V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        fn format_annotation<V: Display>(info: &V) -> String {
            let inner = format!("{}", info);
            if inner.is_empty() {
                inner
            } else {
                format!("[{}]", inner)
            }
        }

        match &self.expr {
            TypeExpr::Bool => write!(f, "bool{}", format_annotation(&self.annotation)),
            TypeExpr::Field => write!(f, "Field{}", format_annotation(&self.annotation)),
            TypeExpr::U32 => write!(f, "u32{}", format_annotation(&self.annotation)),
            TypeExpr::Array(inner, size) => write!(
                f,
                "Array{}<{}, {}>",
                format_annotation(&self.annotation),
                inner,
                size,
            ),
            TypeExpr::Ref(inner) => {
                write!(f, "Ref{}<{}>", format_annotation(&self.annotation), inner)
            }
        }
    }
}

impl<V: CommutativeSemigroup + Display> Type<V> {
    pub fn get_arithmetic_result_type(&self, other: &Self) -> Self {
        match (&self.expr, &other.expr) {
            (TypeExpr::Field, _) | (_, TypeExpr::Field) => {
                Type::field(self.annotation.op(&other.annotation))
            }
            (TypeExpr::U32, _) | (_, TypeExpr::U32) => {
                Type::u32(self.annotation.op(&other.annotation))
            }
            (TypeExpr::Bool, _) | (_, TypeExpr::Bool) => {
                Type::bool(self.annotation.op(&other.annotation))
            }
            _ => panic!("Cannot perform arithmetic on types {} and {}", self, other),
        }
    }

    pub fn combine_with_annotation(self, other: &V) -> Self {
        Type {
            expr: self.expr,
            annotation: self.annotation.op(other),
        }
    }
}

impl<V: Clone> Type<V> {
    pub fn get_array_element(&self) -> Self {
        match &self.expr {
            TypeExpr::Array(inner, _) => *inner.clone(),
            _ => panic!("Type is not an array"),
        }
    }

    pub fn get_pointed(&self) -> Self {
        match &self.expr {
            TypeExpr::Ref(inner) => *inner.clone(),
            _ => panic!("Type is not a reference"),
        }
    }
}

impl<V> Type<V> {
    pub fn get_annotation(&self) -> &V {
        &self.annotation
    }

    pub fn bool(annotation: V) -> Self {
        Type {
            expr: TypeExpr::Bool,
            annotation,
        }
    }

    pub fn field(annotation: V) -> Self {
        Type {
            expr: TypeExpr::Field,
            annotation,
        }
    }

    pub fn u32(annotation: V) -> Self {
        Type {
            expr: TypeExpr::U32,
            annotation,
        }
    }

    pub fn array_of(self, size: usize, annotation: V) -> Self {
        Type {
            expr: TypeExpr::Array(Box::new(self), size),
            annotation,
        }
    }

    pub fn ref_of(self, annotation: V) -> Self {
        Type {
            expr: TypeExpr::Ref(Box::new(self)),
            annotation,
        }
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self.expr, TypeExpr::U32 | TypeExpr::Field | TypeExpr::Bool)
    }

    pub fn is_array(&self) -> bool {
        matches!(self.expr, TypeExpr::Array(_, _))
    }

    pub fn is_u32(&self) -> bool {
        matches!(self.expr, TypeExpr::U32)
    }

    pub fn has_eq(&self) -> bool {
        matches!(self.expr, TypeExpr::Field | TypeExpr::U32 | TypeExpr::Bool)
    }

    pub fn is_ref(&self) -> bool {
        matches!(self.expr, TypeExpr::Ref(_))
    }

    pub fn equal_up_to_annotation(&self, other: &Self) -> bool {
        self.expr.equal_up_to_annotation(&other.expr)
    }

    pub fn is_ref_of(&self, other: &Self) -> bool {
        matches!(&self.expr, TypeExpr::Ref(inner) if inner.as_ref().equal_up_to_annotation(other))
    }

    pub fn get_refered(&self) -> &Self {
        match &self.expr {
            TypeExpr::Ref(inner) => inner.as_ref(),
            _ => panic!("Type is not a reference"),
        }
    }
}
