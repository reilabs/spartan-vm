use crate::compiler::phase1::ssa::{FunctionId, Type, ValueId};

pub enum OpCode {
    Add(ValueId, ValueId, ValueId),
    Lt(ValueId, ValueId, ValueId),

    WriteWitness(ValueId, ValueId),
    IncA(ValueId, ValueId),
    IncB(ValueId, ValueId),
    IncC(ValueId, ValueId),
    SealConstraint,

    FConst(ValueId, ark_bn254::Fr),
    BConst(ValueId, bool),
    UConst(ValueId, u32),

    Call(Vec<ValueId>, FunctionId, Vec<ValueId>),

    ArrayGet(ValueId, ValueId, ValueId),

    Alloc(ValueId, Type),
    Store(ValueId, ValueId),
    Load(ValueId, ValueId),
}


