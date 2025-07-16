pub const LIMBS: usize = 4;


pub enum ArithOp {
    Add,
    Mul,
}

pub enum CmpOp {
    Eq,
    Lt,
}

pub enum OpCode {
    AddF([ValueId; LIMBS], [ValueId; LIMBS], [ValueId; LIMBS]),
    AddU(ValueId, ValueId, ValueId),
    MulF([ValueId; LIMBS], [ValueId; LIMBS], [ValueId; LIMBS]),
    MulU(ValueId, ValueId, ValueId),
}