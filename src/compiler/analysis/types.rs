use std::{collections::HashMap, fmt::Display};

use tracing::{Level, instrument};

use crate::compiler::{
    flow_analysis::{CFG, FlowAnalysis},
    ir::r#type::{CommutativeMonoid, Type},
    ssa::{CastTarget, Const, Function, FunctionId, OpCode, SSA, ValueId},
};

pub struct TypeInfo<V> {
    functions: HashMap<FunctionId, FunctionTypeInfo<V>>,
}

impl<V> TypeInfo<V> {
    pub fn get_function(&self, function_id: FunctionId) -> &FunctionTypeInfo<V> {
        self.functions.get(&function_id).unwrap()
    }
}

pub struct FunctionTypeInfo<V> {
    values: HashMap<ValueId, Type<V>>,
}

impl<V> FunctionTypeInfo<V> {
    pub fn get_value_type(&self, value_id: ValueId) -> &Type<V> {
        self.values.get(&value_id).unwrap()
    }
}

pub struct Types {}

impl Types {
    pub fn new() -> Self {
        Types {}
    }

    pub fn run<V: CommutativeMonoid + Display + Eq + Clone>(
        &self,
        ssa: &SSA<V>,
        cfg: &FlowAnalysis,
    ) -> TypeInfo<V> {
        let mut type_info = TypeInfo {
            functions: HashMap::new(),
        };

        let function_types = ssa
            .iter_functions()
            .map(|(id, func)| (*id, (func.get_param_types(), func.get_returns())))
            .collect::<HashMap<_, _>>();

        for (function_id, function) in ssa.iter_functions() {
            let cfg = cfg.get_function_cfg(*function_id);
            let function_info = self.run_function(function, &function_types, cfg);
            type_info.functions.insert(*function_id, function_info);
        }
        type_info
    }

    #[instrument(skip_all, level = Level::DEBUG, name = "Types::run_function", fields(function = function.get_name()))]
    fn run_function<V: CommutativeMonoid + Display + Eq + Clone>(
        &self,
        function: &Function<V>,
        function_types: &HashMap<FunctionId, (Vec<Type<V>>, &[Type<V>])>,
        cfg: &CFG,
    ) -> FunctionTypeInfo<V> {
        let mut function_info = FunctionTypeInfo {
            values: HashMap::new(),
        };

        for (value_id, const_) in function.iter_consts() {
            match const_ {
                Const::U(size, _) => function_info
                    .values
                    .insert(*value_id, Type::u(*size, V::empty())),
                Const::Field(_) => function_info
                    .values
                    .insert(*value_id, Type::field(V::empty())),
                Const::BoxedField(_) => function_info
                    .values
                    .insert(*value_id, Type::boxed_field(V::empty())),
            };
        }

        for block in cfg.get_domination_pre_order() {
            let block = function.get_block(block);

            for param in block.get_parameters() {
                function_info.values.insert(param.0, param.1.clone());
            }

            for instruction in block.get_instructions() {
                self.run_opcode(instruction, &mut function_info, function_types)
                    .unwrap();
            }
        }

        function_info
    }

    fn run_opcode<V: CommutativeMonoid + Display + Eq + Clone>(
        &self,
        opcode: &OpCode<V>,
        function_info: &mut FunctionTypeInfo<V>,
        function_types: &HashMap<FunctionId, (Vec<Type<V>>, &[Type<V>])>,
    ) -> Result<(), String> {
        match opcode {
            OpCode::Cmp(_kind, result, lhs, rhs) => {
                let lhs_type = function_info.values.get(lhs).ok_or_else(|| {
                    format!(
                        "Left-hand side value {:?} not found in type assignments",
                        lhs
                    )
                })?;
                let rhs_type = function_info.values.get(rhs).ok_or_else(|| {
                    format!(
                        "Right-hand side value {:?} not found in type assignments",
                        rhs
                    )
                })?;
                function_info.values.insert(
                    *result,
                    Type::u(1, lhs_type.get_annotation().op(rhs_type.get_annotation())),
                );
                Ok(())
            }
            OpCode::BinaryArithOp(_kind, result, lhs, rhs) => {
                let lhs_type = function_info.values.get(lhs).ok_or_else(|| {
                    format!(
                        "Left-hand side value {:?} not found in type assignments",
                        lhs
                    )
                })?;
                let rhs_type = function_info.values.get(rhs).ok_or_else(|| {
                    format!(
                        "Right-hand side value {:?} not found in type assignments",
                        rhs
                    )
                })?;
                function_info
                    .values
                    .insert(*result, lhs_type.get_arithmetic_result_type(rhs_type));
                Ok(())
            }
            OpCode::Alloc(result, typ, annotation) => {
                function_info
                    .values
                    .insert(*result, Type::ref_of(typ.clone(), annotation.clone()));
                Ok(())
            }
            OpCode::Store(_, _) => Ok(()),
            OpCode::Load(result, ptr) => {
                let ptr_type = function_info.values.get(ptr).ok_or_else(|| {
                    format!("Pointer value {:?} not found in type assignments", ptr)
                })?;
                if !ptr_type.is_ref() {
                    return Err(format!(
                        "Load operation expects a reference type, got {}",
                        ptr_type
                    ));
                }
                function_info.values.insert(
                    *result,
                    ptr_type
                        .get_refered()
                        .clone()
                        .combine_with_annotation(ptr_type.get_annotation()),
                );
                Ok(())
            }
            OpCode::MemOp(_, _) => Ok(()),
            OpCode::AssertEq(_, _) => Ok(()),
            OpCode::AssertR1C(_, _, _) => Ok(()),
            OpCode::Call(result, fn_id, args) => {
                let (param_types, return_types) = function_types
                    .get(fn_id)
                    .ok_or_else(|| format!("Function {:?} not found", fn_id))?;

                if args.len() != param_types.len() {
                    return Err(format!(
                        "Function {:?} expects {} arguments, got {}",
                        fn_id,
                        param_types.len(),
                        args.len()
                    ));
                }

                if result.len() != return_types.len() {
                    return Err(format!(
                        "Function {:?} expects {} return values, got {}",
                        fn_id,
                        return_types.len(),
                        result.len()
                    ));
                }

                for (ret, ret_type) in result.iter().zip(return_types.iter()) {
                    function_info.values.insert(*ret, ret_type.clone());
                }
                Ok(())
            }
            OpCode::ArrayGet(result, array, _) => {
                let array_type = function_info.values.get(array).ok_or_else(|| {
                    format!("Array value {:?} not found in type assignments", array)
                })?;

                let element_type = array_type.get_array_element();
                function_info.values.insert(
                    *result,
                    element_type.combine_with_annotation(array_type.get_annotation()),
                );
                Ok(())
            }
            OpCode::ArraySet(result, array, _, _) => {
                let array_type = function_info.values.get(array).ok_or_else(|| {
                    format!("Array value {:?} not found in type assignments", array)
                })?;

                function_info.values.insert(*result, array_type.clone());
                Ok(())
            }
            OpCode::Select(result, _cond, then, otherwise) => {
                let then_type = function_info.values.get(then).ok_or_else(|| {
                    format!("Then value {:?} not found in type assignments", then)
                })?;
                let otherwise_type = function_info.values.get(otherwise).ok_or_else(|| {
                    format!(
                        "Otherwise value {:?} not found in type assignments",
                        otherwise
                    )
                })?;
                function_info.values.insert(
                    *result,
                    then_type.get_arithmetic_result_type(otherwise_type),
                );
                Ok(())
            }
            OpCode::WriteWitness(result, value, annotation) => {
                let Some(result) = result else {
                    return Ok(());
                };
                let witness_type = function_info.values.get(value).ok_or_else(|| {
                    format!("Witness value {:?} not found in type assignments", value)
                })?;
                function_info.values.insert(
                    *result,
                    witness_type.clone().combine_with_annotation(annotation),
                );
                Ok(())
            }
            OpCode::FreshWitness(r, tp) => {
                function_info.values.insert(*r, tp.clone());
                Ok(())
            }
            OpCode::Constrain(_, _, _) => Ok(()),
            OpCode::NextDCoeff(v) => {
                function_info.values.insert(*v, Type::field(V::empty()));
                Ok(())
            }
            OpCode::BumpD(_, _, _) => Ok(()),
            OpCode::MkSeq(r, _, top_tp, t) => {
                function_info.values.insert(*r, top_tp.of(t.clone()));
                Ok(())
            }
            OpCode::Cast(result, value, target) => {
                let value_type = function_info
                    .values
                    .get(value)
                    .ok_or_else(|| format!("Value {:?} not found in type assignments", value))?;

                let result_type = match target {
                    CastTarget::Field => Type::field(value_type.get_annotation().clone()),
                    CastTarget::U(size) => Type::u(*size, value_type.get_annotation().clone()),
                };

                function_info.values.insert(*result, result_type);
                Ok(())
            }
            OpCode::Truncate(result, value, _, _) => {
                let value_type = function_info
                    .values
                    .get(value)
                    .ok_or_else(|| format!("Value {:?} not found in type assignments", value))?;

                function_info.values.insert(*result, value_type.clone());
                Ok(())
            }
            OpCode::Not(result, value) => {
                let value_type = function_info
                    .values
                    .get(value)
                    .ok_or_else(|| format!("Value {:?} not found in type assignments", value))?;
                function_info.values.insert(*result, value_type.clone());
                Ok(())
            }
            OpCode::ToBits(result, value, _, output_size) => {
                let value_type = function_info
                    .values
                    .get(value)
                    .ok_or_else(|| format!("Value {:?} not found in type assignments", value))?;
                // Return an array of U(1) values with the same annotation as the input
                let bit_type = Type::u(1, value_type.get_annotation().clone());
                let result_type = Type::array_of(bit_type, *output_size, V::empty());
                function_info.values.insert(*result, result_type);
                Ok(())
            }
            OpCode::BoxField(result, _, annotation) => {
                function_info
                    .values
                    .insert(*result, Type::boxed_field(annotation.clone()));
                Ok(())
            }
            OpCode::UnboxField(result, _) => {
                function_info
                    .values
                    .insert(*result, Type::field(V::empty()));
                Ok(())
            }
            OpCode::MulConst(result, _, var) => {
                let var_type = function_info.values.get(var).unwrap();
                function_info.values.insert(*result, var_type.clone());
                Ok(())
            }
        }
    }
}
