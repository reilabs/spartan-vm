use std::{
    alloc::{self, Layout},
    marker::PhantomData,
    mem,
    str::FromStr,
};

use ark_ff::{AdditiveGroup, BigInt, Field as _, Fp, PrimeField as _};
use noirc_abi::input_parser::InputValue;
use tracing::instrument;

use crate::{
    Field,
    layouts::{ConstraintsLayout, WitnessLayout},
    array::{BoxedLayout, BoxedValue},
    bytecode::{self, AllocationInstrumenter, AllocationType, VM},
};
#[cfg(not(target_arch = "wasm32"))]
use crate::bytecode::OpCode;

pub type Handler = fn(*const u64, Frame, &mut VM);

#[cfg(not(target_arch = "wasm32"))]
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
            // Note: Using alloc (uninitialized) rather than alloc_zeroed
            // This matches native behavior where uninitialized memory contains garbage
            // There appears to be a bug where frame slots are read without being initialized
            // On native, garbage pointers happen to work; on WASM with zeros, they fail
            // TODO: Fix the root cause - ensure all frame slots are initialized before reading
            let data = alloc::alloc(layout) as *mut u64;

            // Check for allocation failure
            if data.is_null() {
                #[cfg(target_arch = "wasm32")]
                web_sys::console::error_1(&format!("[WASM ERROR] Frame allocation failed! size={}", size + 2).into());
                panic!("Frame allocation failed - out of memory");
            }

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

#[cfg(not(target_arch = "wasm32"))]
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

/// Internal implementation shared by both threaded and branching interpreters
fn run_internal<F>(
    program: &[u64],
    witness_layout: WitnessLayout,
    constraints_layout: ConstraintsLayout,
    ordered_inputs: &[InputValue],
    dispatch_fn: F,
) -> WitgenResult
where
    F: FnOnce(*const u64, Frame, &mut VM),
{
    #[cfg(target_arch = "wasm32")]
    web_sys::console::log_1(&format!("[WASM] run_internal: Allocating vectors, wit={}, const={}",
        witness_layout.pre_commitment_size(), constraints_layout.size()).into());

    let mut out_a = vec![Field::ZERO; constraints_layout.size()];
    let mut out_b = vec![Field::ZERO; constraints_layout.size()];
    let mut out_c = vec![Field::ZERO; constraints_layout.size()];

    #[cfg(target_arch = "wasm32")]
    web_sys::console::log_1(&"[WASM] run_internal: Constraint vectors allocated".into());

    let mut out_wit_pre_comm = vec![Field::ZERO; witness_layout.pre_commitment_size()];
    out_wit_pre_comm[0] = Field::ONE;

    #[cfg(target_arch = "wasm32")]
    web_sys::console::log_1(&"[WASM] run_internal: Witness vectors allocated".into());
    let flat_inputs = flatten_param_vec(ordered_inputs);
    for i in 0..flat_inputs.len() {
        out_wit_pre_comm[1 + i] = flat_inputs[i];
    }
    let mut out_wit_post_comm = vec![Field::ZERO; witness_layout.post_commitment_size()];

    #[cfg(target_arch = "wasm32")]
    web_sys::console::log_1(&"[WASM] run_internal: Creating VM".into());

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

    #[cfg(target_arch = "wasm32")]
    web_sys::console::log_1(&format!("[WASM] run_internal: Allocating frame, size={}", program[1]).into());

    let frame = Frame::push(
        program[1],
        Frame {
            data: std::ptr::null_mut(),
        },
        &mut vm,
    );

    #[cfg(target_arch = "wasm32")]
    web_sys::console::log_1(&"[WASM] run_internal: Writing input values".into());

    let mut current_offset = 2 as isize ;
    for (_, el) in ordered_inputs.iter().enumerate() {
        unsafe{current_offset += write_input_value(frame.data.offset(current_offset), el, &mut vm)};
    }

    #[cfg(target_arch = "wasm32")]
    web_sys::console::log_1(&"[WASM] run_internal: Starting dispatch".into());

    let pc = unsafe { program.as_ptr().offset(2) };

    // Call the provided dispatch function
    dispatch_fn(pc, frame, &mut vm);

    #[cfg(target_arch = "wasm32")]
    web_sys::console::log_1(&"[WASM] run_internal: Dispatch completed".into());

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



    WitgenResult {
        out_wit_pre_comm,
        out_wit_post_comm,
        out_a,
        out_b,
        out_c,
        instrumenter: vm.allocation_instrumenter,
    }
}

/// Run witness generation using threaded dispatch (fast, native only)
#[cfg(not(target_arch = "wasm32"))]
#[instrument(skip_all, name = "Interpreter::run")]
pub fn run(
    program: &[u64],
    witness_layout: WitnessLayout,
    constraints_layout: ConstraintsLayout,
    ordered_inputs: &[InputValue],
) -> WitgenResult {
    // Threaded dispatch requires preparing the dispatch table
    let mut program = program.to_vec();
    prepare_dispatch(&mut program);

    run_internal(&program, witness_layout, constraints_layout, ordered_inputs, |pc, frame, vm| {
        dispatch(pc, frame, vm)
    })
}

/// Run witness generation using branching dispatch (WASM-compatible)
#[instrument(skip_all, name = "Interpreter::run_branching")]
pub fn run_branching(
    program: &[u64],
    witness_layout: WitnessLayout,
    constraints_layout: ConstraintsLayout,
    ordered_inputs: &[InputValue],
) -> WitgenResult {
    #[cfg(target_arch = "wasm32")]
    web_sys::console::log_1(&"[WASM] Entering run_branching".into());

    let result = run_internal(program, witness_layout, constraints_layout, ordered_inputs, |pc, frame, vm| {
        bytecode::dispatch_branching(pc, frame, vm)
    });

    #[cfg(target_arch = "wasm32")]
    web_sys::console::log_1(&"[WASM] Exiting run_branching".into());

    result
}

/// Internal implementation shared by both threaded and branching AD interpreters
fn run_ad_internal<F>(
    program: &[u64],
    coeffs: &[Field],
    witness_layout: WitnessLayout,
    constraints_layout: ConstraintsLayout,
    dispatch_fn: F,
) -> (Vec<Field>, Vec<Field>, Vec<Field>, AllocationInstrumenter)
where
    F: FnOnce(*const u64, Frame, &mut VM),
{
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

    let pc = unsafe { program.as_ptr().offset(2) };

    // Call the provided dispatch function
    dispatch_fn(pc, frame, &mut vm);

    (out_da, out_db, out_dc, vm.allocation_instrumenter)
}

/// Run AD using threaded dispatch (fast, native only)
#[cfg(not(target_arch = "wasm32"))]
#[instrument(skip_all, name = "Interpreter::run_ad")]
pub fn run_ad(
    program: &[u64],
    coeffs: &[Field],
    witness_layout: WitnessLayout,
    constraints_layout: ConstraintsLayout,
) -> (Vec<Field>, Vec<Field>, Vec<Field>, AllocationInstrumenter) {
    // Threaded dispatch requires preparing the dispatch table
    let mut program = program.to_vec();
    prepare_dispatch(&mut program);

    run_ad_internal(&program, coeffs, witness_layout, constraints_layout, |pc, frame, vm| {
        dispatch(pc, frame, vm)
    })
}

/// Run AD using branching dispatch (WASM-compatible)
#[instrument(skip_all, name = "Interpreter::run_ad_branching")]
pub fn run_ad_branching(
    program: &[u64],
    coeffs: &[Field],
    witness_layout: WitnessLayout,
    constraints_layout: ConstraintsLayout,
) -> (Vec<Field>, Vec<Field>, Vec<Field>, AllocationInstrumenter) {
    run_ad_internal(program, coeffs, witness_layout, constraints_layout, |pc, frame, vm| {
        bytecode::dispatch_branching(pc, frame, vm)
    })
}


fn write_input_value(ptr: *mut u64, el: &InputValue, vm: &mut VM) -> isize {
    match el {
        InputValue::Field(field_element) => {
            unsafe{*(ptr as *mut Field) = field_element.into_repr();}
            return 4;
        }
        InputValue::Vec(vec) => {
            if vec.len() == 0 {
                let layout = BoxedLayout::array(0, false);
                let array = BoxedValue::alloc(layout, vm);
                unsafe{*(ptr as *mut BoxedValue) = array;}
            } else {
                match &vec[0] {
                    InputValue::Field(_) => {
                        let layout = BoxedLayout::array(vec.len() * 4, false);
                        let array = BoxedValue::alloc(layout, vm);
                        
                        for (elem_ind, input) in vec.iter().enumerate() {
                            let ptr = array.array_idx(elem_ind, 4);
                            write_input_value(ptr, input, vm);
                        }
                        unsafe{*(ptr as *mut BoxedValue) = array;}
                    }
                    InputValue::Vec(_) => {
                        let layout = BoxedLayout::array(vec.len(), true);
                        let array = BoxedValue::alloc(layout, vm);
                        
                        for (elem_ind, input) in vec.iter().enumerate() {
                            let ptr = array.array_idx(elem_ind, 1);
                            write_input_value(ptr, input, vm);
                        }
                        unsafe{*(ptr as *mut BoxedValue) = array;}
                    }
                    _ => panic!("Only field elements are supported in arrays for now"),
                }
            }
            return 1;
        }
        _ => panic!("Unsupported input value type. We only support Field and nested Vecs of Fields for now."),
    }
}

fn flatten_param_vec(vec: &[InputValue]) -> Vec<Field> {
    let mut encoded_value = Vec::new();
    for elem in vec {
        encoded_value.extend(flatten_params(elem));
    }
    encoded_value
}

fn flatten_params(value: &InputValue) -> Vec<Field> {
    let mut encoded_value = Vec::new();
    match value {
        InputValue::Field(elem) => encoded_value.push(elem.into_repr()),

        InputValue::Vec(vec_elements) => {
            for elem in vec_elements {
                encoded_value.extend(flatten_params(elem));
            }
        }
        _ => panic!("Unsupported input value type. We only support Field and nested Vecs of Fields for now."),
    }
    encoded_value
}