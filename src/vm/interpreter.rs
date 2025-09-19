use std::{
    alloc::{self, Layout},
    marker::PhantomData,
    mem,
};

use ark_ff::{AdditiveGroup, BigInt, Fp};
use tracing::instrument;

use crate::{
    compiler::Field,
    vm::{array::BoxedValue, bytecode::{self, AllocationInstrumenter, AllocationType, OpCode, VM}},
};

pub type Handler = fn(*const u64, Frame, &mut VM);

#[inline(always)]
pub fn dispatch(
    pc: *const u64,
    frame: Frame,
    vm: &mut VM,
) {
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
            vm.allocation_instrumenter.alloc(AllocationType::Stack, size as usize + 2);
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
            vm.allocation_instrumenter.free(AllocationType::Stack, size as usize + 2);
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

#[instrument(skip_all, name = "Interpreter::run")]
pub fn run(
    program: &[u64],
    witness_size: usize,
    r1cs_size: usize,
    inputs: &[Field],
) -> (Vec<Field>, Vec<Field>, Vec<Field>, Vec<Field>, AllocationInstrumenter) {

    let mut out_wit = vec![Field::ZERO; witness_size];
    let mut out_a = vec![Field::ZERO; r1cs_size];
    let mut out_b = vec![Field::ZERO; r1cs_size];
    let mut out_c = vec![Field::ZERO; r1cs_size];
    let mut vm = VM::new_witgen(
        out_wit.as_mut_ptr(),
        out_a.as_mut_ptr(),
        out_b.as_mut_ptr(),
        out_c.as_mut_ptr(),
    );

    let frame = Frame::push(
        program[1],
        Frame {
            data: std::ptr::null_mut(),
        },
        &mut vm
    );
    for (i, el) in inputs.iter().enumerate() {
        frame.write_field(2 + (i as isize) * 4, *el);
    }

    let mut program = program.to_vec();
    prepare_dispatch(&mut program);

    let pc = unsafe { program.as_mut_ptr().offset(2) };


    dispatch(
        pc,
        frame,
        &mut vm
    );

    (out_wit, out_a, out_b, out_c, vm.allocation_instrumenter)
}

#[instrument(skip_all, name = "Interpreter::run_ad")]
pub fn run_ad(
    program: &[u64],
    witness_size: usize,
    coeffs: &[Field],
) -> (Vec<Field>, Vec<Field>, Vec<Field>, AllocationInstrumenter) {
    let mut out_da = vec![Field::ZERO; witness_size];
    let mut out_db = vec![Field::ZERO; witness_size];
    let mut out_dc = vec![Field::ZERO; witness_size];
    let mut vm = VM::new_ad(
        out_da.as_mut_ptr(),
        out_db.as_mut_ptr(),
        out_dc.as_mut_ptr(),
        coeffs.as_ptr(),
    );

    let frame = Frame::push(
        program[1],
        Frame {
            data: std::ptr::null_mut(),
        },
        &mut vm
    );

    let mut program = program.to_vec();
    prepare_dispatch(&mut program);

    let pc = unsafe { program.as_mut_ptr().offset(2) };

    dispatch(
        pc,
        frame,
        &mut vm
    );

    (out_da, out_db, out_dc, vm.allocation_instrumenter)

}