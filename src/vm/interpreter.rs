use std::{
    alloc::{self, Layout},
    marker::PhantomData,
    mem,
};

use ark_ff::{AdditiveGroup, BigInt, Fp};
use tracing::instrument;

use crate::{
    compiler::Field,
    vm::bytecode::{self, OpCode},
};

pub type Handler = fn(*const u64, Frame, *mut Field, *mut Field, *mut Field, *mut Field);

#[inline(always)]
pub fn dispatch(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let opcode: Handler = unsafe { mem::transmute(*pc) };
    opcode(pc, frame, out_wit, out_a, out_b, out_c);
}

#[derive(Debug, Copy, Clone)]
pub struct Frame {
    pub data: *mut u64,
}

impl Frame {
    pub fn push(size: u64, parent: Frame) -> Self {
        unsafe {
            let layout = Layout::array::<u64>(size as usize + 2).unwrap();
            let data = alloc::alloc(layout) as *mut u64;
            *data = size;
            *data.offset(1) = parent.data as u64;
            let data = data.offset(2);
            Frame { data }
        }
    }

    #[inline(always)]
    pub fn pop(self) -> Frame {
        unsafe {
            let real_data = self.data.offset(-2);
            let parent_data = *real_data.offset(1) as *mut u64;
            let size = *real_data;
            alloc::dealloc(
                real_data as *mut u8,
                Layout::array::<u64>(size as usize + 2).unwrap(),
            );
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
) -> (Vec<Field>, Vec<Field>, Vec<Field>, Vec<Field>) {
    let frame = Frame::push(
        program[1],
        Frame {
            data: std::ptr::null_mut(),
        },
    );
    for (i, el) in inputs.iter().enumerate() {
        frame.write_field(2 + (i as isize) * 4, *el);
    }

    let mut program = program.to_vec();
    prepare_dispatch(&mut program);

    let pc = unsafe { program.as_mut_ptr().offset(2) };

    let mut out_wit = vec![Field::ZERO; witness_size];
    let mut out_a = vec![Field::ZERO; r1cs_size];
    let mut out_b = vec![Field::ZERO; r1cs_size];
    let mut out_c = vec![Field::ZERO; r1cs_size];

    dispatch(
        pc,
        frame,
        out_wit.as_mut_ptr(),
        out_a.as_mut_ptr(),
        out_b.as_mut_ptr(),
        out_c.as_mut_ptr(),
    );

    (out_wit, out_a, out_b, out_c)
}
