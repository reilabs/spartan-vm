use std::{
    alloc::{self, Layout},
    marker::PhantomData,
    mem,
    str::FromStr,
};

use ark_ff::{AdditiveGroup, BigInt, Field as _, Fp, PrimeField as _};
use noirc_abi::input_parser::InputValue;
use tracing::{field, instrument};

use crate::{
    compiler::{
        Field,
        r1cs_gen::{ConstraintsLayout, WitnessLayout},
    },
    vm::{
        array::{BoxedLayout, BoxedValue},
        bytecode::{self, AllocationInstrumenter, AllocationType, OpCode, VM},
    },
};

pub type Handler = fn(*const u64, Frame, &mut VM);

#[inline(always)]
pub fn dispatch(pc: *const u64, frame: Frame, vm: &mut VM) {
    let opcode: Handler = unsafe { mem::transmute(*pc) };
    opcode(pc, frame, vm);
}

#[derive(Debug, Copy, Clone)]
pub struct Frame {
    pub data: *mut u64,
}

impl Frame {
    pub fn push(size: u64, parent: Frame, vm: &mut VM) -> Self {
        unsafe {
            let layout = Layout::array::<u64>(size as usize + 2).unwrap();
            let data = alloc::alloc(layout) as *mut u64;
            *data = size;
            *data.offset(1) = parent.data as u64;
            let data = data.offset(2);
            vm.allocation_instrumenter
                .alloc(AllocationType::Stack, size as usize + 2);
            Frame { data }
        }
    }

    #[inline(always)]
    pub fn pop(self, vm: &mut VM) -> Frame {
        unsafe {
            let real_data = self.data.offset(-2);
            let parent_data = *real_data.offset(1) as *mut u64;
            let size = *real_data;
            alloc::dealloc(
                real_data as *mut u8,
                Layout::array::<u64>(size as usize + 2).unwrap(),
            );
            vm.allocation_instrumenter
                .free(AllocationType::Stack, size as usize + 2);
            Frame { data: parent_data }
        }
    }

    #[inline(always)]
    pub fn read_field(&self, offset: isize) -> Field {
        let a0 = unsafe { *self.data.offset(offset) };
        let a1 = unsafe { *self.data.offset(offset + 1) };
        let a2 = unsafe { *self.data.offset(offset + 2) };
        let a3 = unsafe { *self.data.offset(offset + 3) };
        Fp(BigInt([a0, a1, a2, a3]), PhantomData)
    }

    #[inline(always)]
    pub fn read_field_mut(&self, offset: isize) -> *mut Field {
        unsafe { self.data.offset(offset) as *mut Field }
    }

    #[inline(always)]
    pub fn read_u64_mut(&self, offset: isize) -> *mut u64 {
        unsafe { self.data.offset(offset) }
    }

    #[inline(always)]
    pub fn read_u64(&self, offset: isize) -> u64 {
        unsafe { *self.data.offset(offset) }
    }

    #[inline(always)]
    pub fn read_bool(&self, offset: isize) -> bool {
        let a0 = unsafe { *self.data.offset(offset) };
        a0 != 0
    }

    #[inline(always)]
    pub fn read_ptr<A>(&self, offset: isize) -> *mut A {
        unsafe { *self.data.offset(offset) as *mut A }
    }

    #[inline(always)]
    pub fn read_array(&self, offset: isize) -> BoxedValue {
        unsafe { *self.read_array_mut(offset) }
    }

    #[inline(always)]
    pub fn read_array_mut(&self, offset: isize) -> *mut BoxedValue {
        unsafe { self.data.offset(offset) as *mut BoxedValue }
    }

    #[inline(always)]
    pub fn write_u64(&self, offset: isize, value: u64) {
        unsafe {
            *self.data.offset(offset) = value;
        };
    }

    #[inline(always)]
    pub fn write_field(&self, offset: isize, field: Field) {
        let a0 = field.0.0[0];
        let a1 = field.0.0[1];
        let a2 = field.0.0[2];
        let a3 = field.0.0[3];
        unsafe {
            *self.data.offset(offset) = a0;
            *self.data.offset(offset + 1) = a1;
            *self.data.offset(offset + 2) = a2;
            *self.data.offset(offset + 3) = a3;
        }
    }

    #[inline(always)]
    pub fn memcpy(&self, dest: isize, src: isize, size: usize) {
        unsafe {
            std::ptr::copy_nonoverlapping(self.data.offset(src), self.data.offset(dest), size);
        }
    }

    #[inline(always)]
    pub fn write_to(&self, dst: *mut u64, src: isize, size: usize) {
        unsafe {
            std::ptr::copy_nonoverlapping(self.data.offset(src), dst, size);
        }
    }
}

fn prepare_dispatch(program: &mut [u64]) {
    let mut current_offset = 0;
    while current_offset < program.len() {
        let opcode = program[current_offset];
        if opcode == u64::MAX {
            current_offset += 2;
            continue;
        }
        let next = OpCode::next_opcode(program, current_offset);
        program[current_offset] = bytecode::DISPATCH[opcode as usize] as u64;
        current_offset = next;
    }
}

pub struct WitgenResult {
    pub out_wit_pre_comm: Vec<Field>,
    pub out_wit_post_comm: Vec<Field>,
    pub out_a: Vec<Field>,
    pub out_b: Vec<Field>,
    pub out_c: Vec<Field>,
    pub instrumenter: AllocationInstrumenter,
}

fn fix_multiplicities_section(wit: &mut [Field], witness_layout: WitnessLayout) {
    for i in witness_layout.multiplicities_start()..witness_layout.multiplicities_end() {
        // We used this as a *mut u64 when writing multiplicities, so we need to convert to an actual field element
        wit[i] = Field::from(wit[i].0.0[0]);
    }
}

#[derive(Debug, Clone)]
pub enum InputValueOrdered {
    Field(Field),
    String(String),
    Vec(Vec<InputValueOrdered>),
    Struct(Vec<(String, InputValueOrdered)>),
}

impl InputValueOrdered {
    pub fn field_sizes (&self) -> Vec<usize> {
        match self {
            InputValueOrdered::Field(_) => vec![4],
            InputValueOrdered::String(_) => panic!("Strings are not supported in element_size"),
            InputValueOrdered::Vec(_) => vec![1],
            InputValueOrdered::Struct(fields) => {
                let mut total_size = vec![];
                for (_field_name, field_value) in fields {
                    total_size.extend(field_value.field_sizes());
                }
                total_size
            }
        }
    }

    pub fn need_reference_counting(&self) -> Vec<bool> {
        match self {
            InputValueOrdered::Field(_) => vec![false],
            InputValueOrdered::String(_) => panic!("Strings are not supported in need_reference_counting"),
            InputValueOrdered::Vec(_) => vec![true], 
            InputValueOrdered::Struct(fields) => {
                let mut reference_counting = vec![];
                for (_field_name, field_value) in fields {
                    reference_counting.extend(field_value.need_reference_counting());
                }
                reference_counting
            }
        }
    }
}

#[instrument(skip_all, name = "Interpreter::run")]
pub fn run(
    program: &[u64],
    witness_layout: WitnessLayout,
    constraints_layout: ConstraintsLayout,
    ordered_inputs: &[InputValueOrdered],
) -> WitgenResult {
    let mut out_a = vec![Field::ZERO; constraints_layout.size()];
    let mut out_b = vec![Field::ZERO; constraints_layout.size()];
    let mut out_c = vec![Field::ZERO; constraints_layout.size()];
    let mut out_wit_pre_comm = vec![Field::ZERO; witness_layout.pre_commitment_size()];
    out_wit_pre_comm[0] = Field::ONE;
    let flat_inputs = flatten_param_vec(ordered_inputs);
    for i in 0..flat_inputs.len() {
        out_wit_pre_comm[1 + i] = flat_inputs[i];
    }
    let mut out_wit_post_comm = vec![Field::ZERO; witness_layout.post_commitment_size()];
    let mut vm = VM::new_witgen(
        out_a.as_mut_ptr(),
        out_b.as_mut_ptr(),
        out_c.as_mut_ptr(),
        unsafe {
            out_wit_pre_comm
                .as_mut_ptr()
                .offset(1 + flat_inputs.len() as isize)
        },
        unsafe {
            out_wit_pre_comm
                .as_mut_ptr()
                .offset(witness_layout.multiplicities_start() as isize)
        },
        unsafe {
            out_a
                .as_mut_ptr()
                .offset(constraints_layout.lookups_data_start() as isize)
        },
        unsafe {
            out_b
                .as_mut_ptr()
                .offset(constraints_layout.lookups_data_start() as isize)
        },
        constraints_layout.tables_data_start(),
        witness_layout.tables_data_start() - witness_layout.challenges_start(),
    );

    let frame = Frame::push(
        program[1],
        Frame {
            data: std::ptr::null_mut(),
        },
        &mut vm,
    );

    let mut current_offset = 2 as isize ;
    for (_, el) in ordered_inputs.iter().enumerate() {
        unsafe{current_offset += write_input_value(frame.data.offset(current_offset), el.clone(), &mut vm)};
    }

    let mut program = program.to_vec();
    prepare_dispatch(&mut program);

    let pc = unsafe { program.as_mut_ptr().offset(2) };

    dispatch(pc, frame, &mut vm);

    fix_multiplicities_section(&mut out_wit_pre_comm, witness_layout);

    let mut random =
        Field::from_bigint(BigInt::from_str("18765435241434657586764563434227903").unwrap())
            .unwrap();
    for i in 0..witness_layout.challenges_size {
        // so random, wow
        out_wit_post_comm[i] = random;
        random = (random + Field::from(17)) * random;
    }

    let mut running_prod = Field::from(1);
    for tbl in vm.tables.iter() {
        if tbl.num_indices != 1 || tbl.num_values != 0 {
            todo!("wide tables");
        }

        let alpha = out_wit_post_comm[0];
        for i in 0..tbl.length {
            let multiplicity = unsafe { *tbl.multiplicities_wit.offset(i as isize) };
            let denom = alpha - Field::from(i as u64);
            out_b[tbl.elem_inverses_constraint_section_offset + i] = denom;
            out_c[tbl.elem_inverses_constraint_section_offset + i] = multiplicity;
            if multiplicity != Field::ZERO {
                // Skip all of inversion logic, it's just zero
                out_a[tbl.elem_inverses_constraint_section_offset + i] = running_prod;
                running_prod *= denom;
            }
        }
    }

    let mut running_inv = running_prod.inverse().unwrap();

    for tbl in vm.tables.iter().rev() {
        if tbl.num_indices != 1 || tbl.num_values != 0 {
            todo!("wide tables");
        }

        for i in (0..tbl.length).rev() {
            let multiplicity = out_c[tbl.elem_inverses_constraint_section_offset + i];
            let denom = out_b[tbl.elem_inverses_constraint_section_offset + i];
            let running_prod = out_a[tbl.elem_inverses_constraint_section_offset + i];

            if multiplicity != Field::ZERO {
                let elem = running_prod * running_inv;
                out_a[tbl.elem_inverses_constraint_section_offset + i] = elem;
                running_inv *= denom;
            }
        }
    }

    let mut current_lookup_off = 0;

    while current_lookup_off < constraints_layout.lookups_data_size {
        let cnst_off = constraints_layout.lookups_data_start() + current_lookup_off;
        let wit_off = witness_layout.lookups_data_start() - witness_layout.challenges_start() + current_lookup_off;

        let table_ix = out_a[cnst_off].0.0[0];
        let table = &vm.tables[table_ix as usize];
        if table.num_indices != 1 || table.num_values != 0 {
            todo!("wide tables");
        }
        let ix_in_table = out_b[cnst_off].0.0[0];
        out_a[cnst_off] = out_a[table.elem_inverses_constraint_section_offset + ix_in_table as usize];
        out_b[cnst_off] = out_b[table.elem_inverses_constraint_section_offset + ix_in_table as usize];
        out_c[cnst_off] = Field::ONE;
        out_wit_post_comm[wit_off] = out_a[cnst_off];
        out_c[table.elem_inverses_constraint_section_offset + table.length] += out_a[cnst_off];

        current_lookup_off += 1;
    }

    for tbl in vm.tables.iter() {
        if tbl.num_indices != 1 || tbl.num_values != 0 {
            todo!("wide tables");
        }
        for i in 0..tbl.length {
            let multiplicity = out_c[tbl.elem_inverses_constraint_section_offset + i];
            if multiplicity != Field::ZERO {
                let elem = out_a[tbl.elem_inverses_constraint_section_offset + i] * multiplicity;
                out_a[tbl.elem_inverses_constraint_section_offset + i] = elem;
                out_wit_post_comm[tbl.elem_inverses_witness_section_offset + i] = elem;
                out_a[tbl.elem_inverses_constraint_section_offset + tbl.length] += elem;
            }
        }
        out_b[tbl.elem_inverses_constraint_section_offset + tbl.length] = Field::ONE;

    }



    let result = WitgenResult {
        out_wit_pre_comm,
        out_wit_post_comm,
        out_a,
        out_b,
        out_c,
        instrumenter: vm.allocation_instrumenter,
    };

    result
}

#[instrument(skip_all, name = "Interpreter::run_ad")]
pub fn run_ad(
    program: &[u64],
    coeffs: &[Field],
    witness_layout: WitnessLayout,
    constraints_layout: ConstraintsLayout,
) -> (Vec<Field>, Vec<Field>, Vec<Field>, AllocationInstrumenter) {
    let mut out_da = vec![Field::ZERO; witness_layout.size()];
    let mut out_db = vec![Field::ZERO; witness_layout.size()];
    let mut out_dc = vec![Field::ZERO; witness_layout.size()];
    let mut vm = VM::new_ad(
        out_da.as_mut_ptr(),
        out_db.as_mut_ptr(),
        out_dc.as_mut_ptr(),
        coeffs.as_ptr(),
        witness_layout,
        constraints_layout,
    );

    let frame = Frame::push(
        program[1],
        Frame {
            data: std::ptr::null_mut(),
        },
        &mut vm,
    );

    // for (i, el) in bytecode::DISPATCH.iter().enumerate() {
    //     println!("{}: {:?}", i, el);
    // }

    let mut program = program.to_vec();
    prepare_dispatch(&mut program);

    let pc = unsafe { program.as_mut_ptr().offset(2) };

    dispatch(pc, frame, &mut vm);

    (out_da, out_db, out_dc, vm.allocation_instrumenter)
}

fn dissolve_struct(el: InputValueOrdered) -> InputValueOrdered {
    match el {
        InputValueOrdered::Field(_) => el,
        InputValueOrdered::String(_) => panic!("Strings are not supported in dissolve_struct"),
        InputValueOrdered::Struct(fields) => {
            let new_fields = fields
                .into_iter()
                .flat_map(|(field_name, field_value)| {
                    let dissolved = dissolve_struct(field_value);
                    match dissolved {
                        InputValueOrdered::Struct(nested_fields) => nested_fields
                            .into_iter()
                            .map(|(nested_field_name, nested_value)| (field_name.clone()+"_"+&nested_field_name, nested_value))
                            .collect::<Vec<_>>(),
                        other => vec![(field_name, other)],
                    }
                })
                .collect();
            InputValueOrdered::Struct(new_fields)
        }
        InputValueOrdered::Vec(vec) => dissolve_vec(vec),
    }
}

fn dissolve_vec(vec: Vec<InputValueOrdered>) -> InputValueOrdered {
    if vec.is_empty() {
        return InputValueOrdered::Vec(vec![]);
    }

    let first_dissolved = dissolve_struct(vec[0].clone());
    match first_dissolved {
        InputValueOrdered::Struct(fields) if fields.len() == 1 => {
            // Single-field struct array: unwrap to just the field values
            let dissolved_vec = vec
                .into_iter()
                .map(|inner_struct| {
                    let dissolved = dissolve_struct(inner_struct);
                    match dissolved {
                        InputValueOrdered::Struct(mut nested_fields) => nested_fields.remove(0).1,
                        _ => panic!("Expected struct inside array of structs"),
                    }
                })
                .collect();
            InputValueOrdered::Vec(dissolved_vec)
        }
        InputValueOrdered::Struct(_) => {
            // Multi-field struct array: dissolve each element
            let dissolved_vec = vec.into_iter().map(dissolve_struct).collect();
            InputValueOrdered::Vec(dissolved_vec)
        }
        _ => InputValueOrdered::Vec(vec),
    }
}

fn write_input_value(ptr: *mut u64, el: InputValueOrdered, vm: &mut VM) -> isize {
    let el = dissolve_struct(el);
    match el {
        InputValueOrdered::Field(field_element) => {
            unsafe { *(ptr as *mut Field) = field_element; }
            4
        }
        InputValueOrdered::Vec(vec) => {
            write_vec_input(ptr, vec, vm);
            1
        }
        InputValueOrdered::Struct(elements) => {
            let mut accumulated_offset = 0;
            for (_field_name, input) in elements {
                unsafe {
                    accumulated_offset += write_input_value(ptr.offset(accumulated_offset), input, vm);
                }
            }
            accumulated_offset
        }
        InputValueOrdered::String(_) => panic!(
            "Unsupported input value type. We only support Field and nested Vecs of Fields for now."
        ),
    }
}

fn write_vec_input(ptr: *mut u64, vec: Vec<InputValueOrdered>, vm: &mut VM) {
    if vec.is_empty() {
        let layout = BoxedLayout::array(0, false);
        let array = BoxedValue::alloc(layout, vm);
        unsafe { *(ptr as *mut BoxedValue) = array; }
        return;
    }

    match &vec[0] {
        InputValueOrdered::Field(_) => write_field_array(ptr, vec, vm),
        InputValueOrdered::Vec(_) => write_nested_array(ptr, vec, vm),
        InputValueOrdered::Struct(_) => write_struct_array(ptr, vec, vm),
        InputValueOrdered::String(_) => panic!("Unexpected input value type in array"),
    }
}

fn write_field_array(ptr: *mut u64, vec: Vec<InputValueOrdered>, vm: &mut VM) {
    let layout = BoxedLayout::array(vec.len() * 4, false);
    let array = BoxedValue::alloc(layout, vm);

    for (elem_ind, input) in vec.into_iter().enumerate() {
        let elem_ptr = array.array_idx(elem_ind, 4);
        write_input_value(elem_ptr, input, vm);
    }
    unsafe { *(ptr as *mut BoxedValue) = array; }
}

fn write_nested_array(ptr: *mut u64, vec: Vec<InputValueOrdered>, vm: &mut VM) {
    let layout = BoxedLayout::array(vec.len(), true);
    let array = BoxedValue::alloc(layout, vm);

    for (elem_ind, input) in vec.into_iter().enumerate() {
        let elem_ptr = array.array_idx(elem_ind, 1);
        write_input_value(elem_ptr, input, vm);
    }
    unsafe { *(ptr as *mut BoxedValue) = array; }
}

fn write_struct_array(ptr: *mut u64, vec: Vec<InputValueOrdered>, vm: &mut VM) {
    let array_layout = BoxedLayout::array(vec.len(), true);
    let array = BoxedValue::alloc(array_layout, vm);

    let field_sizes = vec[0].field_sizes();
    let reference_counting = vec[0].need_reference_counting();
    let tuple_layout = BoxedLayout::new_struct(field_sizes.clone(), reference_counting);

    for (array_ind, tuple) in vec.into_iter().enumerate() {
        let array_ptr = array.array_idx(array_ind, 1);
        let new_tuple = BoxedValue::alloc(tuple_layout, vm);

        let tuple_fields = match tuple {
            InputValueOrdered::Struct(f) => f,
            _ => panic!("Expected struct inside array of structs"),
        };

        for (elem_ind, (_field_name, input)) in tuple_fields.into_iter().enumerate() {
            write_input_value(new_tuple.tuple_idx(elem_ind, &field_sizes), input, vm);
        }
        unsafe { *(array_ptr as *mut BoxedValue) = new_tuple; }
    }
    unsafe { *(ptr as *mut BoxedValue) = array; }
}

fn flatten_param_vec(vec: &[InputValueOrdered]) -> Vec<Field> {
    let mut encoded_value = Vec::new();
    for elem in vec {
        encoded_value.extend(flatten_params(elem));
    }
    encoded_value
}

fn flatten_params(value: &InputValueOrdered) -> Vec<Field> {
    let mut encoded_value = Vec::new();
    match value {
        InputValueOrdered::Field(elem) => encoded_value.push(*elem),

        InputValueOrdered::Vec(vec_elements) => {
            for elem in vec_elements {
                encoded_value.extend(flatten_params(elem));
            }
        }

        InputValueOrdered::Struct(fields) => {
            for (_field_name, field_value) in fields {
                encoded_value.extend(flatten_params(field_value));
            }
        }
        _ => panic!(
            "Unsupported input value type. We only support Field, Vecs, and Structs for now."
        ),
    }
    encoded_value
}
