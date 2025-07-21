use tracing::{Level, instrument};

use crate::compiler::{
    ir::r#type::Type, ssa::{
        BinaryArithOpKind, BlockId, CastTarget, CmpKind, Const, Endianness, FunctionId, SeqType, Terminator, SSA
    }, Field
};

pub trait Value<Context, Taint>
where
    Self: Sized + Clone,
{
    fn cmp(&self, b: &Self, cmp_kind: CmpKind, out_type: &Type<Taint>, ctx: &mut Context) -> Self;
    fn arith(
        &self,
        b: &Self,
        binary_arith_op_kind: BinaryArithOpKind,
        out_type: &Type<Taint>,
        ctx: &mut Context,
    ) -> Self;
    fn assert_eq(&self, other: &Self, ctx: &mut Context);
    fn assert_r1c(a: &Self, b: &Self, c: &Self, ctx: &mut Context);
    fn array_get(&self, index: &Self, out_type: &Type<Taint>, ctx: &mut Context) -> Self;
    fn array_set(
        &self,
        index: &Self,
        value: &Self,
        out_type: &Type<Taint>,
        ctx: &mut Context,
    ) -> Self;
    fn truncate(&self, _from: usize, to: usize, out_type: &Type<Taint>, ctx: &mut Context) -> Self;
    fn cast(&self, cast_target: &CastTarget, out_type: &Type<Taint>, ctx: &mut Context) -> Self;
    fn constrain(a: &Self, b: &Self, c: &Self, ctx: &mut Context);
    fn to_bits(
        &self,
        endianness: Endianness,
        size: usize,
        out_type: &Type<Taint>,
        ctx: &mut Context,
    ) -> Self;
    fn not(&self, out_type: &Type<Taint>, ctx: &mut Context) -> Self;
    fn of_u(s: usize, v: u128, ctx: &mut Context) -> Self;
    fn of_field(f: Field, ctx: &mut Context) -> Self;
    fn mk_array(a: Vec<Self>, ctx: &mut Context, seq_type: SeqType, elem_type: &Type<Taint>) -> Self;
    fn alloc(ctx: &mut Context) -> Self;
    fn ptr_write(&self, val: &Self, ctx: &mut Context);
    fn ptr_read(&self, out_type: &Type<Taint>, ctx: &mut Context) -> Self;
    fn expect_constant_bool(&self, ctx: &mut Context) -> bool;
    fn select(&self, if_t: &Self, if_f: &Self, out_type: &Type<Taint>, ctx: &mut Context) -> Self;
    fn write_witness(&self, tp: Option<&Type<Taint>>, ctx: &mut Context) -> Self;
}

pub trait Context<V, Taint> {
    // If this returns Some, the function execution will be skipped and the returned values will be used instead
    // as call results.
    fn on_call(
        &mut self,
        func: FunctionId,
        params: &mut [V],
        param_types: &[&Type<Taint>],
    ) -> Option<Vec<V>>;
    fn on_return(&mut self, returns: &mut [V], return_types: &[Type<Taint>]);
    fn on_jmp(&mut self, target: BlockId, params: &mut [V], param_types: &[&Type<Taint>]);
}

pub struct SymbolicExecutor {}

impl SymbolicExecutor {
    pub fn new() -> Self {
        Self {}
    }

    #[instrument(skip_all, name = "SymbolicExecutor::run", level = Level::DEBUG)]
    pub fn run<V, T, Ctx>(
        &self,
        ssa: &SSA<T>,
        entry_point: FunctionId,
        params: Vec<V>,
        context: &mut Ctx,
    ) where
        V: Value<Ctx, T>,
        Ctx: Context<V, T>,
        T: Clone,
    {
        self.run_fn(ssa, entry_point, params, context);
    }

    #[instrument(skip_all, name="SymbolicExecutor::run_fn", level = Level::TRACE, fields(function = %ssa.get_function(fn_id).get_name()))]
    fn run_fn<V, T, Ctx>(
        &self,
        ssa: &SSA<T>,
        fn_id: FunctionId,
        mut inputs: Vec<V>,
        ctx: &mut Ctx,
    ) -> Vec<V>
    where
        V: Value<Ctx, T>,
        Ctx: Context<V, T>,
        T: Clone,
    {
        let fn_body = ssa.get_function(fn_id);
        let entry = fn_body.get_entry();
        let mut scope: Vec<Option<V>> = vec![None; fn_body.get_var_num_bound()];

        for (val, cst) in fn_body.iter_consts() {
            let v = match cst {
                Const::U(s, v) => V::of_u(*s, *v, ctx),
                Const::Field(f) => V::of_field(f.clone(), ctx),
            };
            scope[val.0 as usize] = Some(v);
        }

        let call_result = ctx.on_call(
            fn_id,
            &mut inputs,
            &entry.get_parameters().map(|(_, tp)| tp).collect::<Vec<_>>(),
        );

        if let Some(call_result) = call_result {
            return call_result;
        }

        for (pval, ppos) in inputs.iter_mut().zip(entry.get_parameter_values()) {
            scope[ppos.0 as usize] = Some(pval.clone());
        }

        let mut current = Some(entry);

        while let Some(block) = current {
            for instr in block.get_instructions() {
                match instr {
                    crate::compiler::ssa::OpCode::Cmp(cmp_kind, r, a, b) => {
                        let a = scope[a.0 as usize].as_ref().unwrap();
                        let b = scope[b.0 as usize].as_ref().unwrap();
                        scope[r.0 as usize] =
                            Some(a.cmp(b, *cmp_kind, &fn_body.get_value_type(*r).unwrap(), ctx));
                    }
                    crate::compiler::ssa::OpCode::BinaryArithOp(binary_arith_op_kind, r, a, b) => {
                        let a = scope[a.0 as usize].as_ref().unwrap();
                        let b = scope[b.0 as usize].as_ref().unwrap();
                        scope[r.0 as usize] = Some(a.arith(
                            b,
                            *binary_arith_op_kind,
                            &fn_body.get_value_type(*r).unwrap(),
                            ctx,
                        ));
                    }
                    crate::compiler::ssa::OpCode::Cast(r, a, cast_target) => {
                        let a = scope[a.0 as usize].as_ref().unwrap();
                        scope[r.0 as usize] =
                            Some(a.cast(cast_target, &fn_body.get_value_type(*r).unwrap(), ctx));
                    }
                    crate::compiler::ssa::OpCode::Truncate(r, a, to, from) => {
                        let a = scope[a.0 as usize].as_ref().unwrap();
                        scope[r.0 as usize] =
                            Some(a.truncate(*from, *to, &fn_body.get_value_type(*r).unwrap(), ctx));
                    }
                    crate::compiler::ssa::OpCode::Not(r, a) => {
                        let a = scope[a.0 as usize].as_ref().unwrap();
                        scope[r.0 as usize] =
                            Some(a.not(&fn_body.get_value_type(*r).unwrap(), ctx));
                    }
                    crate::compiler::ssa::OpCode::MkSeq(r, a, seq_type, elem_type) => {
                        let a = a
                            .iter()
                            .map(|id| scope[id.0 as usize].as_ref().unwrap().clone())
                            .collect::<Vec<_>>();
                        scope[r.0 as usize] = Some(V::mk_array(a, ctx, *seq_type, elem_type));
                    }
                    crate::compiler::ssa::OpCode::Alloc(r, _, _) => {
                        scope[r.0 as usize] = Some(V::alloc(ctx));
                    }
                    crate::compiler::ssa::OpCode::Store(ptr, val) => {
                        let ptr = scope[ptr.0 as usize].as_ref().unwrap();
                        let val = scope[val.0 as usize].as_ref().unwrap();
                        ptr.ptr_write(val, ctx);
                    }
                    crate::compiler::ssa::OpCode::Load(r, ptr) => {
                        let ptr = scope[ptr.0 as usize].as_ref().unwrap();
                        scope[r.0 as usize] =
                            Some(ptr.ptr_read(&fn_body.get_value_type(*r).unwrap(), ctx));
                    }
                    crate::compiler::ssa::OpCode::AssertR1C(a, b, c) => {
                        let a = scope[a.0 as usize].as_ref().unwrap();
                        let b = scope[b.0 as usize].as_ref().unwrap();
                        let c = scope[c.0 as usize].as_ref().unwrap();
                        V::assert_r1c(a, b, c, ctx);
                    }
                    crate::compiler::ssa::OpCode::Call(returns, function_id, arguments) => {
                        let params = arguments
                            .iter()
                            .map(|id| scope[id.0 as usize].as_ref().unwrap().clone())
                            .collect::<Vec<_>>();
                        let outputs = self.run_fn(ssa, *function_id, params, ctx);
                        for (i, val) in returns.iter().enumerate() {
                            scope[val.0 as usize] = Some(outputs[i].clone());
                        }
                    }
                    crate::compiler::ssa::OpCode::ArrayGet(r, a, i) => {
                        let a = scope[a.0 as usize].as_ref().unwrap();
                        let i = scope[i.0 as usize].as_ref().unwrap();
                        scope[r.0 as usize] =
                            Some(a.array_get(i, &fn_body.get_value_type(*r).unwrap(), ctx));
                    }
                    crate::compiler::ssa::OpCode::ArraySet(r, arr, i, v) => {
                        let a = scope[arr.0 as usize].as_ref().unwrap();
                        let i = scope[i.0 as usize].as_ref().unwrap();
                        let v = scope[v.0 as usize].as_ref().unwrap();
                        scope[r.0 as usize] =
                            Some(a.array_set(i, v, &fn_body.get_value_type(*r).unwrap(), ctx));
                    }
                    crate::compiler::ssa::OpCode::Select(r, cond, if_t, if_f) => {
                        let cond = scope[cond.0 as usize].as_ref().unwrap();
                        let if_t = scope[if_t.0 as usize].as_ref().unwrap();
                        let if_f = scope[if_f.0 as usize].as_ref().unwrap();
                        scope[r.0 as usize] = Some(cond.select(
                            if_t,
                            if_f,
                            &fn_body.get_value_type(*r).unwrap(),
                            ctx,
                        ));
                    }
                    crate::compiler::ssa::OpCode::ToBits(r, a, endianness, size) => {
                        let a = scope[a.0 as usize].as_ref().unwrap();
                        scope[r.0 as usize] = Some(a.to_bits(
                            *endianness,
                            *size,
                            &fn_body.get_value_type(*r).unwrap(),
                            ctx,
                        ));
                    }
                    crate::compiler::ssa::OpCode::WriteWitness(r, a, _) => {
                        let a = scope[a.0 as usize].as_ref().unwrap();
                        if let Some(r) = r {
                            scope[r.0 as usize] =
                                Some(a.write_witness(fn_body.get_value_type(*r), ctx));
                        } else {
                            a.write_witness(None, ctx);
                        }
                    }
                    crate::compiler::ssa::OpCode::Constrain(a, b, c) => {
                        let a = scope[a.0 as usize].as_ref().unwrap();
                        let b = scope[b.0 as usize].as_ref().unwrap();
                        let c = scope[c.0 as usize].as_ref().unwrap();
                        V::constrain(a, b, c, ctx);
                    }
                    crate::compiler::ssa::OpCode::AssertEq(a, b) => {
                        let a = scope[a.0 as usize].as_ref().unwrap();
                        let b = scope[b.0 as usize].as_ref().unwrap();
                        V::assert_eq(a, b, ctx);
                    }
                }
            }

            match block.get_terminator().unwrap() {
                Terminator::Return(returns) => {
                    let mut outputs = returns
                        .iter()
                        .map(|id| scope[id.0 as usize].as_ref().unwrap().clone())
                        .collect::<Vec<_>>();
                    ctx.on_return(&mut outputs, &fn_body.get_returns());
                    return outputs;
                }
                Terminator::Jmp(target, params) => {
                    let mut params = params
                        .iter()
                        .map(|id| scope[id.0 as usize].as_ref().unwrap().clone())
                        .collect::<Vec<_>>();
                    let target_block = fn_body.get_block(*target);
                    let target_params = target_block.get_parameter_values();
                    ctx.on_jmp(
                        *target,
                        &mut params,
                        &target_block
                            .get_parameters()
                            .map(|(_, tp)| tp)
                            .collect::<Vec<_>>(),
                    );
                    for (i, val) in target_params.zip(params.into_iter()) {
                        scope[i.0 as usize] = Some(val);
                    }
                    current = Some(target_block);
                }
                Terminator::JmpIf(cond, if_true, if_false) => {
                    let cond = scope[cond.0 as usize].as_ref().unwrap();
                    if cond.expect_constant_bool(ctx) {
                        current = Some(fn_body.get_block(*if_true));
                    } else {
                        current = Some(fn_body.get_block(*if_false));
                    }
                }
            }
        }

        panic!("ICE: Unreachable, function did not return");
    }
}
