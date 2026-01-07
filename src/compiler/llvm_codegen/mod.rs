//! LLVM Code Generation for Spartan VM SSA
//!
//! This module translates Spartan VM's SSA representation into LLVM IR,
//! which can then be compiled to native code or WebAssembly.

mod field_ops;
mod types;

use std::collections::HashMap;
use std::path::Path;

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetTriple,
};
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType};
use inkwell::values::{
    BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue,
};
use inkwell::AddressSpace;
use inkwell::IntPredicate;
use inkwell::OptimizationLevel;

use crate::compiler::analysis::types::{FunctionTypeInfo, TypeInfo};
use crate::compiler::flow_analysis::{FlowAnalysis, CFG};
use crate::compiler::ir::r#type::{Type, TypeExpr};
use crate::compiler::ssa::{
    BinaryArithOpKind, Block, BlockId, CmpKind, Const, Function, FunctionId, Terminator, ValueId,
    SSA,
};
use crate::compiler::taint_analysis::ConstantTaint;

use self::field_ops::FieldOps;
use self::types::TypeConverter;

/// VM struct containing output pointers
/// struct VM { field_ptr[4] }
pub struct VMType<'ctx> {
    /// The LLVM struct type for VM
    pub struct_type: inkwell::types::StructType<'ctx>,
    /// Pointer type to VM
    pub ptr_type: inkwell::types::PointerType<'ctx>,
}

impl<'ctx> VMType<'ctx> {
    /// Number of output field pointers in the VM struct
    pub const NUM_OUTPUT_PTRS: usize = 4;

    pub fn new(context: &'ctx Context, field_type: inkwell::types::ArrayType<'ctx>) -> Self {
        // VM struct contains 4 pointers to field elements
        // Each field element is [4 x i64], so pointer to that
        let field_ptr_type = context.ptr_type(AddressSpace::default());

        // Create struct with 4 field pointers
        let field_types: Vec<inkwell::types::BasicTypeEnum> = (0..Self::NUM_OUTPUT_PTRS)
            .map(|_| field_ptr_type.into())
            .collect();

        let struct_type = context.struct_type(&field_types, false);
        let ptr_type = context.ptr_type(AddressSpace::default());

        Self { struct_type, ptr_type }
    }

    /// Get a pointer to the nth output field from a VM pointer
    pub fn get_output_ptr(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: PointerValue<'ctx>,
        index: u32,
        name: &str,
    ) -> PointerValue<'ctx> {
        assert!((index as usize) < Self::NUM_OUTPUT_PTRS);

        // Get pointer to the field within the VM struct
        let field_ptr_ptr = builder
            .build_struct_gep(self.struct_type, vm_ptr, index, &format!("{}_ptr_ptr", name))
            .unwrap();

        // Load the pointer value
        let ptr_type = builder.get_insert_block().unwrap().get_context().ptr_type(AddressSpace::default());
        builder
            .build_load(ptr_type, field_ptr_ptr, &format!("{}_ptr", name))
            .unwrap()
            .into_pointer_value()
    }
}

/// LLVM Code Generator for Spartan VM SSA
pub struct LLVMCodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    type_converter: TypeConverter<'ctx>,
    field_ops: FieldOps<'ctx>,
    vm_type: VMType<'ctx>,

    /// Maps SSA ValueIds to LLVM values within the current function
    value_map: HashMap<ValueId, BasicValueEnum<'ctx>>,

    /// Maps SSA BlockIds to LLVM basic blocks within the current function
    block_map: HashMap<BlockId, inkwell::basic_block::BasicBlock<'ctx>>,

    /// Maps SSA FunctionIds to LLVM functions
    function_map: HashMap<FunctionId, FunctionValue<'ctx>>,

    /// The VM pointer for the current function
    vm_ptr: Option<PointerValue<'ctx>>,
}

impl<'ctx> LLVMCodeGen<'ctx> {
    /// Create a new LLVM code generator
    pub fn new(context: &'ctx Context, module_name: &str) -> Self {
        let module = context.create_module(module_name);
        let builder = context.create_builder();
        let type_converter = TypeConverter::new(context);
        let field_ops = FieldOps::new(context, &module);

        // Create VM type with field array type
        let field_type = context.i64_type().array_type(types::FIELD_LIMBS);
        let vm_type = VMType::new(context, field_type);

        Self {
            context,
            module,
            builder,
            type_converter,
            field_ops,
            vm_type,
            value_map: HashMap::new(),
            block_map: HashMap::new(),
            function_map: HashMap::new(),
            vm_ptr: None,
        }
    }

    /// Compile SSA to LLVM IR
    pub fn compile(
        &mut self,
        ssa: &SSA<ConstantTaint>,
        flow_analysis: &FlowAnalysis,
        type_info: &TypeInfo<ConstantTaint>,
    ) {
        // First pass: declare all functions
        for (fn_id, function) in ssa.iter_functions() {
            self.declare_function(*fn_id, function, type_info);
        }

        // Second pass: generate function bodies
        for (fn_id, function) in ssa.iter_functions() {
            let cfg = flow_analysis.get_function_cfg(*fn_id);
            let fn_type_info = type_info.get_function(*fn_id);
            self.compile_function(*fn_id, function, cfg, fn_type_info);
        }
    }

    /// Declare a function (create its signature without body)
    fn declare_function(
        &mut self,
        fn_id: FunctionId,
        function: &Function<ConstantTaint>,
        type_info: &TypeInfo<ConstantTaint>,
    ) {
        let fn_type_info = type_info.get_function(fn_id);
        let entry = function.get_entry();

        // Build parameter types - first parameter is always VM*
        let mut param_types: Vec<BasicMetadataTypeEnum> = Vec::new();
        param_types.push(self.vm_type.ptr_type.into()); // VM* as first param

        // Add the regular function parameters
        // Use param_type() to get pointer types for fields (cross-platform ABI)
        for (_, tp) in entry.get_parameters() {
            param_types.push(self.type_converter.param_type(tp).into());
        }

        // Build return type - for now, we'll return a struct if multiple values
        let return_types: Vec<BasicTypeEnum> = function
            .get_returns()
            .iter()
            .map(|tp| self.type_converter.convert_type(tp))
            .collect();

        let fn_type = if return_types.is_empty() {
            self.context.void_type().fn_type(&param_types, false)
        } else if return_types.len() == 1 {
            return_types[0].fn_type(&param_types, false)
        } else {
            // Multiple returns - use a struct
            let return_struct = self.context.struct_type(&return_types, false);
            return_struct.fn_type(&param_types, false)
        };

        // Rename "main" to "spartan_main" to avoid conflicts with C main()
        let name = if function.get_name() == "main" {
            "spartan_main"
        } else {
            function.get_name()
        };
        let fn_value = self.module.add_function(name, fn_type, None);
        self.function_map.insert(fn_id, fn_value);
    }

    /// Compile a single function
    fn compile_function(
        &mut self,
        fn_id: FunctionId,
        function: &Function<ConstantTaint>,
        cfg: &CFG,
        type_info: &FunctionTypeInfo<ConstantTaint>,
    ) {
        // Clear per-function state
        self.value_map.clear();
        self.block_map.clear();

        let fn_value = self.function_map[&fn_id];
        let entry = function.get_entry();
        let entry_block_id = function.get_entry_id();

        // Create entry block first (LLVM requires entry block to be first)
        let entry_bb = self.context.append_basic_block(fn_value, &format!("block_{}", entry_block_id.0));
        self.block_map.insert(entry_block_id, entry_bb);

        // Create remaining basic blocks
        for (block_id, _) in function.get_blocks() {
            if *block_id != entry_block_id {
                let block_name = format!("block_{}", block_id.0);
                let bb = self.context.append_basic_block(fn_value, &block_name);
                self.block_map.insert(*block_id, bb);
            }
        }

        // Map entry block parameters to function arguments
        let entry_bb = self.block_map[&function.get_entry_id()];
        self.builder.position_at_end(entry_bb);

        // Allocate scratch space for field operations at function entry
        // This avoids stack growth from repeated alloca in loops
        self.field_ops.init_scratch(&self.builder);

        // First parameter is always VM*
        self.vm_ptr = Some(fn_value.get_nth_param(0).unwrap().into_pointer_value());

        // Map SSA parameters to LLVM function arguments (starting from index 1)
        // For pointer-passed parameters (field types), load the value from the pointer
        for (i, (param_id, param_type)) in entry.get_parameters().enumerate() {
            let param_value = fn_value.get_nth_param((i + 1) as u32).unwrap();

            let mapped_value = if self.type_converter.should_pass_by_pointer(param_type) {
                // Load field value from pointer
                let field_type = self.type_converter.convert_type(param_type);
                self.builder
                    .build_load(field_type, param_value.into_pointer_value(), &format!("param_{}", i))
                    .unwrap()
            } else {
                param_value
            };

            self.value_map.insert(*param_id, mapped_value);
        }

        // Generate constants
        for (val_id, constant) in function.iter_consts() {
            let value = self.compile_const(constant);
            self.value_map.insert(*val_id, value);
        }

        // Track phi nodes that need incoming values: (target_block, param_index) -> PhiValue
        let mut phi_nodes: HashMap<(BlockId, usize), inkwell::values::PhiValue<'ctx>> = HashMap::new();

        // Generate code for each block in dominator order
        for block_id in cfg.get_domination_pre_order() {
            self.compile_block_with_phis(function, block_id, type_info, &mut phi_nodes);
        }

        // Now add incoming values to phi nodes
        for (block_id, block) in function.get_blocks() {
            if let Some(terminator) = block.get_terminator() {
                let current_bb = self.block_map[block_id];
                match terminator {
                    Terminator::Jmp(target_id, args) => {
                        for (i, arg_id) in args.iter().enumerate() {
                            if let Some(phi) = phi_nodes.get(&(*target_id, i)) {
                                if let Some(arg_val) = self.value_map.get(arg_id) {
                                    phi.add_incoming(&[(arg_val, current_bb)]);
                                }
                            }
                        }
                    }
                    Terminator::JmpIf(_, true_target, false_target) => {
                        // JmpIf doesn't pass arguments to targets in this SSA
                    }
                    Terminator::Return(_) => {}
                }
            }
        }

        // Clear scratch space for next function
        self.field_ops.clear_scratch();
    }

    /// Compile a block, tracking phi nodes for later
    fn compile_block_with_phis(
        &mut self,
        function: &Function<ConstantTaint>,
        block_id: BlockId,
        type_info: &FunctionTypeInfo<ConstantTaint>,
        phi_nodes: &mut HashMap<(BlockId, usize), inkwell::values::PhiValue<'ctx>>,
    ) {
        let block = function.get_block(block_id);
        let bb = self.block_map[&block_id];

        // If this isn't the entry block, we need to handle block parameters (phi nodes)
        if block_id != function.get_entry_id() {
            self.builder.position_at_end(bb);

            // Block parameters become phi nodes
            for (i, (param_id, param_type)) in block.get_parameters().enumerate() {
                let llvm_type = self.type_converter.convert_type(param_type);
                let phi = self.builder.build_phi(llvm_type, &format!("v{}", param_id.0)).unwrap();
                self.value_map.insert(*param_id, phi.as_basic_value());
                phi_nodes.insert((block_id, i), phi);
            }
        }

        self.builder.position_at_end(bb);

        // Generate instructions
        for instruction in block.get_instructions() {
            self.compile_instruction(instruction, type_info);
        }

        // Generate terminator
        if let Some(terminator) = block.get_terminator() {
            self.compile_terminator(function, block_id, terminator);
        }
    }

    /// Compile a constant value
    fn compile_const(&self, constant: &Const) -> BasicValueEnum<'ctx> {
        match constant {
            Const::U(bits, value) => {
                let int_type = self.context.custom_width_int_type(*bits as u32);
                int_type.const_int(*value as u64, false).into()
            }
            Const::Field(field_val) => {
                // Field is represented as [4 x i64] in Montgomery form
                self.field_ops.const_field(field_val)
            }
            Const::BoxedField(field_val) => {
                // BoxedField is a pointer to a field - for now, treat similarly
                self.field_ops.const_field(field_val)
            }
        }
    }

    /// Compile a single instruction
    fn compile_instruction(
        &mut self,
        instruction: &crate::compiler::ssa::OpCode<ConstantTaint>,
        type_info: &FunctionTypeInfo<ConstantTaint>,
    ) {
        use crate::compiler::ssa::OpCode;

        match instruction {
            OpCode::BinaryArithOp {
                kind,
                result,
                lhs,
                rhs,
            } => {
                let lhs_val = self.value_map[lhs];
                let rhs_val = self.value_map[rhs];
                let result_type = type_info.get_value_type(*result);

                let result_val = match &result_type.expr {
                    TypeExpr::Field | TypeExpr::BoxedField => {
                        self.compile_field_binop(*kind, lhs_val, rhs_val)
                    }
                    TypeExpr::U(_) => {
                        self.compile_int_binop(*kind, lhs_val, rhs_val)
                    }
                    _ => panic!("Unsupported type for binary op: {:?}", result_type),
                };

                self.value_map.insert(*result, result_val);
            }

            OpCode::Cmp { kind, result, lhs, rhs } => {
                let lhs_val = self.value_map[lhs].into_int_value();
                let rhs_val = self.value_map[rhs].into_int_value();

                let predicate = match kind {
                    CmpKind::Lt => IntPredicate::ULT,
                    CmpKind::Eq => IntPredicate::EQ,
                };

                let cmp_result = self
                    .builder
                    .build_int_compare(predicate, lhs_val, rhs_val, &format!("v{}", result.0))
                    .unwrap();

                self.value_map.insert(*result, cmp_result.into());
            }

            OpCode::Cast { result, value, target } => {
                let val = self.value_map[value];
                let result_type = type_info.get_value_type(*result);
                let source_type = type_info.get_value_type(*value);

                let result_val = self.compile_cast(val, &source_type, &result_type);
                self.value_map.insert(*result, result_val);
            }

            OpCode::Truncate { result, value, to_bits, .. } => {
                let val = self.value_map[value];
                let target_type = self.context.custom_width_int_type(*to_bits as u32);

                let result_val = if val.is_int_value() {
                    self.builder
                        .build_int_truncate(val.into_int_value(), target_type, &format!("v{}", result.0))
                        .unwrap()
                        .into()
                } else {
                    // Field to int truncation - extract low bits
                    self.field_ops.truncate_to_int(&self.builder, val, *to_bits)
                };

                self.value_map.insert(*result, result_val);
            }

            OpCode::Not { result, value } => {
                let val = self.value_map[value].into_int_value();
                let result_val = self.builder.build_not(val, &format!("v{}", result.0)).unwrap();
                self.value_map.insert(*result, result_val.into());
            }

            OpCode::Select { result, cond, if_t, if_f } => {
                let cond_val = self.value_map[cond].into_int_value();
                let true_val = self.value_map[if_t];
                let false_val = self.value_map[if_f];

                // Convert condition to i1
                let cond_bool = self
                    .builder
                    .build_int_compare(
                        IntPredicate::NE,
                        cond_val,
                        cond_val.get_type().const_zero(),
                        "cond_bool",
                    )
                    .unwrap();

                let result_val = self
                    .builder
                    .build_select(cond_bool, true_val, false_val, &format!("v{}", result.0))
                    .unwrap();

                self.value_map.insert(*result, result_val);
            }

            OpCode::Call { results, function, args } => {
                let fn_value = self.function_map[function];

                // Build argument list - VM* first, then regular args
                let mut arg_values: Vec<BasicMetadataValueEnum> = Vec::new();
                arg_values.push(self.vm_ptr.unwrap().into()); // Pass VM* to callee
                for arg in args {
                    arg_values.push(self.value_map[arg].into());
                }

                let call_result = self
                    .builder
                    .build_call(fn_value, &arg_values, "call_result")
                    .unwrap();

                if results.len() == 1 {
                    if let Some(ret_val) = call_result.try_as_basic_value().basic() {
                        self.value_map.insert(results[0], ret_val);
                    }
                } else if results.len() > 1 {
                    // Multiple returns - extract from struct
                    if let Some(ret_val) = call_result.try_as_basic_value().basic() {
                        for (i, result_id) in results.iter().enumerate() {
                            let extracted = self
                                .builder
                                .build_extract_value(
                                    ret_val.into_struct_value(),
                                    i as u32,
                                    &format!("v{}", result_id.0),
                                )
                                .unwrap();
                            self.value_map.insert(*result_id, extracted);
                        }
                    }
                }
            }

            OpCode::MkSeq { result, elems, seq_type, elem_type } => {
                // Create array on stack
                let elem_llvm_type = self.type_converter.convert_type(elem_type);
                let array_type = elem_llvm_type.array_type(elems.len() as u32);
                let array_ptr = self
                    .builder
                    .build_alloca(array_type, &format!("v{}", result.0))
                    .unwrap();

                // Store elements
                for (i, elem_id) in elems.iter().enumerate() {
                    let elem_val = self.value_map[elem_id];
                    let idx = self.context.i64_type().const_int(i as u64, false);
                    let elem_ptr = unsafe {
                        self.builder
                            .build_in_bounds_gep(
                                array_type,
                                array_ptr,
                                &[self.context.i64_type().const_zero(), idx],
                                "elem_ptr",
                            )
                            .unwrap()
                    };
                    self.builder.build_store(elem_ptr, elem_val).unwrap();
                }

                self.value_map.insert(*result, array_ptr.into());
            }

            OpCode::ArrayGet { result, array, index } => {
                let array_ptr = self.value_map[array].into_pointer_value();
                let index_val = self.value_map[index].into_int_value();
                let result_type = type_info.get_value_type(*result);
                let elem_type = self.type_converter.convert_type(&result_type);

                let elem_ptr = unsafe {
                    self.builder
                        .build_in_bounds_gep(
                            elem_type,
                            array_ptr,
                            &[index_val],
                            "array_elem_ptr",
                        )
                        .unwrap()
                };

                let loaded = self
                    .builder
                    .build_load(elem_type, elem_ptr, &format!("v{}", result.0))
                    .unwrap();

                self.value_map.insert(*result, loaded);
            }

            OpCode::ArraySet { result, array, index, value } => {
                // ArraySet returns a new array (immutable semantics)
                // For now, we'll do a copy-on-write style implementation
                let array_ptr = self.value_map[array].into_pointer_value();
                let index_val = self.value_map[index].into_int_value();
                let new_value = self.value_map[value];
                let elem_type = self.type_converter.convert_type(type_info.get_value_type(*value));

                // For simplicity, modify in place (caller must ensure COW if needed)
                let elem_ptr = unsafe {
                    self.builder
                        .build_in_bounds_gep(
                            elem_type,
                            array_ptr,
                            &[index_val],
                            "array_set_ptr",
                        )
                        .unwrap()
                };

                self.builder.build_store(elem_ptr, new_value).unwrap();
                self.value_map.insert(*result, array_ptr.into());
            }

            OpCode::Constrain { a, b, c } => {
                // R1CS constraint: a * b = c
                // Write the three constraint values to VM output slots 1, 2, 3
                let a_val = self.value_map[a];
                let b_val = self.value_map[b];
                let c_val = self.value_map[c];
                let vm_ptr = self.vm_ptr.unwrap();

                self.field_ops.write_a(&self.builder, vm_ptr, a_val);
                self.field_ops.write_b(&self.builder, vm_ptr, b_val);
                self.field_ops.write_c(&self.builder, vm_ptr, c_val);
            }

            OpCode::WriteWitness { result, value, .. } => {
                let val = self.value_map[value];
                let vm_ptr = self.vm_ptr.unwrap();

                // Call __write_witness(vm, value) to write and advance pointer
                self.field_ops.write_witness(&self.builder, vm_ptr, val);

                // Map result if present
                if let Some(result_id) = result {
                    self.value_map.insert(*result_id, val);
                }
            }

            OpCode::AssertEq { lhs, rhs } => {
                let lhs_val = self.value_map[lhs];
                let rhs_val = self.value_map[rhs];

                // Generate assertion
                if lhs_val.is_int_value() {
                    let cmp = self
                        .builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            lhs_val.into_int_value(),
                            rhs_val.into_int_value(),
                            "assert_eq_cmp",
                        )
                        .unwrap();

                    // For now, we could call an assert intrinsic or trap
                    // This is a placeholder - in production you'd want proper error handling
                } else {
                    self.field_ops.assert_eq(&self.builder, lhs_val, rhs_val);
                }
            }

            // Memory operations - simplified for now
            OpCode::Alloc { result, elem_type, .. } => {
                let llvm_type = self.type_converter.convert_type(elem_type);
                let ptr = self
                    .builder
                    .build_alloca(llvm_type, &format!("v{}", result.0))
                    .unwrap();
                self.value_map.insert(*result, ptr.into());
            }

            OpCode::Store { ptr, value } => {
                let ptr_val = self.value_map[ptr].into_pointer_value();
                let val = self.value_map[value];
                self.builder.build_store(ptr_val, val).unwrap();
            }

            OpCode::Load { result, ptr } => {
                let ptr_val = self.value_map[ptr].into_pointer_value();
                let result_type = type_info.get_value_type(*result);
                let llvm_type = self.type_converter.convert_type(&result_type);
                let loaded = self
                    .builder
                    .build_load(llvm_type, ptr_val, &format!("v{}", result.0))
                    .unwrap();
                self.value_map.insert(*result, loaded);
            }

            // Operations we'll skip or stub for now
            OpCode::MemOp { .. } => {
                // Reference counting - no-op for basic LLVM
            }

            OpCode::FreshWitness { result, result_type } => {
                // Fresh witness - in LLVM mode, this should read from input
                // For now, create an undefined value
                let llvm_type = self.type_converter.convert_type(result_type);
                let undef = llvm_type.const_zero();
                self.value_map.insert(*result, undef);
            }

            OpCode::BoxField { result, value, .. } => {
                // Boxing - for now just pass through
                let val = self.value_map[value];
                self.value_map.insert(*result, val);
            }

            OpCode::UnboxField { result, value } => {
                let val = self.value_map[value];
                self.value_map.insert(*result, val);
            }

            OpCode::ToBits { result, value, count, .. } => {
                // Convert value to array of bits
                let val = self.value_map[value];
                let bits_array = self.field_ops.to_bits(&self.builder, val, *count);
                self.value_map.insert(*result, bits_array);
            }

            _ => {
                // For unhandled opcodes, we'll need to implement them as needed
                panic!("Unhandled opcode in LLVM: {:?}", instruction);
            }
        }
    }

    /// Compile integer binary operation
    fn compile_int_binop(
        &self,
        kind: BinaryArithOpKind,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let lhs_int = lhs.into_int_value();
        let rhs_int = rhs.into_int_value();

        let result = match kind {
            BinaryArithOpKind::Add => self.builder.build_int_add(lhs_int, rhs_int, "add").unwrap(),
            BinaryArithOpKind::Sub => self.builder.build_int_sub(lhs_int, rhs_int, "sub").unwrap(),
            BinaryArithOpKind::Mul => self.builder.build_int_mul(lhs_int, rhs_int, "mul").unwrap(),
            BinaryArithOpKind::Div => self.builder.build_int_unsigned_div(lhs_int, rhs_int, "div").unwrap(),
            BinaryArithOpKind::And => self.builder.build_and(lhs_int, rhs_int, "and").unwrap(),
        };

        result.into()
    }

    /// Compile field binary operation
    fn compile_field_binop(
        &self,
        kind: BinaryArithOpKind,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        match kind {
            BinaryArithOpKind::Add => self.field_ops.add(&self.builder, lhs, rhs),
            BinaryArithOpKind::Sub => self.field_ops.sub(&self.builder, lhs, rhs),
            BinaryArithOpKind::Mul => self.field_ops.mul(&self.builder, lhs, rhs),
            BinaryArithOpKind::Div => self.field_ops.div(&self.builder, lhs, rhs),
            BinaryArithOpKind::And => panic!("Bitwise AND not supported for field elements"),
        }
    }

    /// Compile a cast operation
    fn compile_cast(
        &self,
        val: BasicValueEnum<'ctx>,
        from_type: &Type<ConstantTaint>,
        to_type: &Type<ConstantTaint>,
    ) -> BasicValueEnum<'ctx> {
        match (&from_type.expr, &to_type.expr) {
            (TypeExpr::U(from_bits), TypeExpr::U(to_bits)) => {
                let int_val = val.into_int_value();
                let target_type = self.context.custom_width_int_type(*to_bits as u32);

                if to_bits > from_bits {
                    self.builder.build_int_z_extend(int_val, target_type, "zext").unwrap().into()
                } else if to_bits < from_bits {
                    self.builder.build_int_truncate(int_val, target_type, "trunc").unwrap().into()
                } else {
                    val
                }
            }
            (TypeExpr::U(_), TypeExpr::Field) => {
                self.field_ops.from_int(&self.builder, val.into_int_value())
            }
            (TypeExpr::Field, TypeExpr::U(bits)) => {
                self.field_ops.truncate_to_int(&self.builder, val, *bits)
            }
            _ => val, // Identity or unsupported
        }
    }

    /// Compile a terminator instruction
    fn compile_terminator(
        &mut self,
        function: &Function<ConstantTaint>,
        current_block_id: BlockId,
        terminator: &Terminator,
    ) {
        match terminator {
            Terminator::Jmp(target_id, args) => {
                let target_bb = self.block_map[target_id];
                let target_block = function.get_block(*target_id);

                // Add incoming values to phi nodes
                // Note: Phi node handling is complex - for now we rely on mem2reg
                // In a full implementation, we'd add incoming values here

                self.builder.build_unconditional_branch(target_bb).unwrap();
            }

            Terminator::JmpIf(cond, true_target, false_target) => {
                let cond_val = self.value_map[cond].into_int_value();
                let true_bb = self.block_map[true_target];
                let false_bb = self.block_map[false_target];

                self.builder
                    .build_conditional_branch(cond_val, true_bb, false_bb)
                    .unwrap();
            }

            Terminator::Return(values) => {
                if values.is_empty() {
                    self.builder.build_return(None).unwrap();
                } else if values.len() == 1 {
                    let ret_val = self.value_map[&values[0]];
                    self.builder.build_return(Some(&ret_val)).unwrap();
                } else {
                    // Multiple returns - pack into struct
                    let ret_values: Vec<BasicValueEnum> =
                        values.iter().map(|v| self.value_map[v]).collect();

                    let ret_types: Vec<BasicTypeEnum> =
                        ret_values.iter().map(|v| v.get_type()).collect();

                    let struct_type = self.context.struct_type(&ret_types, false);
                    let mut struct_val = struct_type.get_undef();

                    for (i, val) in ret_values.iter().enumerate() {
                        struct_val = self
                            .builder
                            .build_insert_value(struct_val, *val, i as u32, "ret_pack")
                            .unwrap()
                            .into_struct_value();
                    }

                    self.builder.build_return(Some(&struct_val)).unwrap();
                }
            }
        }
    }

    /// Get the compiled LLVM IR as a string
    pub fn get_ir(&self) -> String {
        self.module.print_to_string().to_string()
    }

    /// Write LLVM IR to a file
    pub fn write_ir(&self, path: &Path) {
        self.module.print_to_file(path).unwrap();
    }

    /// Compile to WebAssembly
    pub fn compile_to_wasm(&self, path: &Path, optimization: OptimizationLevel) {
        use std::process::Command;

        Target::initialize_webassembly(&InitializationConfig::default());

        let target_triple = TargetTriple::create("wasm32-unknown-unknown");
        let target = Target::from_triple(&target_triple).unwrap();

        let target_machine = target
            .create_target_machine(
                &target_triple,
                "generic",
                "",
                optimization,
                RelocMode::Default,
                CodeModel::Default,
            )
            .unwrap();

        // First write to an object file
        let obj_path = path.with_extension("o");
        target_machine
            .write_to_file(&self.module, FileType::Object, &obj_path)
            .unwrap();

        // Link with wasm-ld to produce final WASM module with exports
        // Find wasm-ld: try LLVM prefix from env, then fall back to PATH
        let wasm_ld = std::env::var("LLVM_SYS_211_PREFIX")
            .map(|prefix| {
                let path = std::path::PathBuf::from(&prefix).join("bin").join("wasm-ld");
                if path.exists() {
                    path.to_string_lossy().to_string()
                } else {
                    "wasm-ld".to_string()
                }
            })
            .unwrap_or_else(|_| "wasm-ld".to_string());

        let status = Command::new(&wasm_ld)
            .args([
                "--no-entry",               // No entry point (we call main explicitly)
                "--export=spartan_main",    // Export main function
                "--import-memory",     // Import memory from host
                "--allow-undefined",   // Allow undefined symbols (will be imported)
                "-o",
            ])
            .arg(path)
            .arg(&obj_path)
            .status()
            .expect(&format!("Failed to run wasm-ld (tried: {}). Make sure LLVM with wasm-ld is installed and either in PATH or LLVM_SYS_211_PREFIX is set.", wasm_ld));

        if !status.success() {
            panic!("wasm-ld failed with status: {}", status);
        }

        // Clean up object file
        std::fs::remove_file(&obj_path).ok();
    }

    /// Get the LLVM module
    pub fn get_module(&self) -> &Module<'ctx> {
        &self.module
    }
}
