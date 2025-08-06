use std::{
    alloc::{self, Layout},
    marker::PhantomData,
    mem,
};

use ark_ff::{AdditiveGroup, BigInt, Fp};
use tracing::instrument;

use crate::compiler::Field;

const DISPATCH_SIZE: usize = 30;

type Handler = fn(*const u64, Frame, *mut Field, *mut Field, *mut Field, *mut Field);

const DISPATCH: [Handler; DISPATCH_SIZE] = [
    mov_const,
    add_f,
    mul_f,
    add_u,
    lt_u,
    write_witness,
    r1c,
    todo,
    mov_mem,
    jmp,
    jmp_if,
    ret,
    call,
    write_ptr,
    nop,
    todo,
    todo,
    todo,
    todo,
    sub_f,
    todo,
    todo,
    todo,
    todo,
    todo,
    todo,
    todo,
    todo,
    todo,
    todo,
];

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
    data: *mut u64,
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
    pub fn read_u64_mut(&self, offset: isize) -> *mut u64 {
        unsafe {
            self.data.offset(offset)
        }
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

pub fn add_f(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let r_offset = unsafe { *pc.offset(1) as isize };
    let a_offset = unsafe { *pc.offset(2) as isize };
    let b_offset = unsafe { *pc.offset(3) as isize };

    let a = frame.read_field(a_offset);
    let b = frame.read_field(b_offset);

    let c = a + b;

    frame.write_field(r_offset, c);

    let new_pc = unsafe { pc.offset(4) };

    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c)
}

pub fn sub_f(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let r_offset = unsafe { *pc.offset(1) as isize };
    let a_offset = unsafe { *pc.offset(2) as isize };
    let b_offset = unsafe { *pc.offset(3) as isize };

    let a = frame.read_field(a_offset);
    let b = frame.read_field(b_offset);

    let c = a - b;

    frame.write_field(r_offset, c);

    let new_pc = unsafe { pc.offset(4) };

    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c)
}

pub fn add_u(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let size = unsafe { *pc.offset(1) as usize };
    let r_offset = unsafe { *pc.offset(2) as isize };
    let a_offset = unsafe { *pc.offset(3) as isize };
    let b_offset = unsafe { *pc.offset(4) as isize };

    let a = frame.read_u64(a_offset);
    let b = frame.read_u64(b_offset);

    let c = a + b;

    // println!("add_u: {}({}) + {}({}) = {}({})", a, a_offset, b, b_offset, c, r_offset);

    frame.write_u64(r_offset, c);

    let new_pc = unsafe { pc.offset(5) };
    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c)
}

pub fn call(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let target = unsafe { *pc.offset(1) as isize };
    let target_pc = unsafe { pc.offset(target) };
    let target_frame_size = unsafe { *pc.offset(target - 1) };
    let args_count = unsafe { *pc.offset(2) as usize };
    let ret_offset = unsafe { *pc.offset(3) as isize };
    let ret_data_ptr = unsafe { frame.data.offset(ret_offset) };
    let ret_pc = unsafe { pc.offset(4 + 2 * args_count as isize) };

    println!("alloc frame of size {} for target {}", target_frame_size, target);
    let new_frame = Frame::push(target_frame_size, frame);

    unsafe {
        *new_frame.data = ret_data_ptr as u64;
        *new_frame.data.offset(1) = ret_pc as u64;
    }

    let mut current_parent = unsafe { new_frame.data.offset(2) };
    let mut current_pc = unsafe { pc.offset(4) };

    for _ in 0..args_count {
        let size = unsafe { *current_pc as usize };
        let arg_offset = unsafe { *current_pc.offset(1) as isize };
        current_pc = unsafe { current_pc.offset(2) };

        frame.write_to(
            current_parent,
            arg_offset,
            size,
        );

        current_parent = unsafe { current_parent.offset(size as isize) };
    }

    dispatch(target_pc, new_frame, out_wit, out_a, out_b, out_c)
}

pub fn ret(
    _pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let ret_address = unsafe { *frame.data.offset(1) } as *mut u64;
    let new_frame = frame.pop();
    if new_frame.data.is_null() {
        return;
    }
    dispatch(ret_address, new_frame, out_wit, out_a, out_b, out_c)
}

pub fn todo(
    _pc: *const u64,
    _frame: Frame,
    _out_wit: *mut Field,
    _out_a: *mut Field,
    _out_b: *mut Field,
    _out_c: *mut Field,
) {
    panic!("todo");
}

pub fn mov_const(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let r_offset = unsafe { *pc.offset(1) as isize };
    let val = unsafe { *pc.offset(2) };
    unsafe {
        *frame.data.offset(r_offset) = val;
    }

    let new_pc = unsafe { pc.offset(3) };
    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c)
}

pub fn write_ptr(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let ptr_slot = unsafe { *pc.offset(1) as isize };
    let ptr = frame.read_u64(ptr_slot) as *mut u64;
    let off = unsafe { *pc.offset(2) as isize };
    let ptr = unsafe { ptr.offset(off) };
    let src = unsafe { *pc.offset(3) as isize };
    let size = unsafe { *pc.offset(4) as usize };
    frame.write_to(ptr, src, size);

    let new_pc = unsafe { pc.offset(5) };
    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c)
}

pub fn r1c(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let a_offset = unsafe { *pc.offset(1) as isize };
    let b_offset = unsafe { *pc.offset(2) as isize };
    let c_offset = unsafe { *pc.offset(3) as isize };

    let a = frame.read_field(a_offset);
    let b = frame.read_field(b_offset);
    let c = frame.read_field(c_offset);

    unsafe {
        *out_a = a;
        *out_b = b;
        *out_c = c;
    }

    let out_a = unsafe { out_a.offset(1) };
    let out_b = unsafe { out_b.offset(1) };
    let out_c = unsafe { out_c.offset(1) };

    let new_pc = unsafe { pc.offset(4) };
    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c);
}

pub fn write_witness(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let offset = unsafe { *pc.offset(1) as isize };
    let value = frame.read_field(offset);
    unsafe {
        *out_wit = value;
    }
    let out_wit = unsafe { out_wit.offset(1) };
    let new_pc = unsafe { pc.offset(2) };
    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c);
}

pub fn nop(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let new_pc = unsafe { pc.offset(1) };
    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c)
}

pub fn mov_mem(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let size = unsafe { *pc.offset(1) as usize };
    let dest = unsafe { *pc.offset(2) as isize };
    let src = unsafe { *pc.offset(3) as isize };

    // println!("mov {} words from {} to {}", size, src, dest);
    frame.memcpy(dest, src, size);

    // println!("frame at dst: {:?}", frame.read_u64(dest));

    let new_pc = unsafe { pc.offset(4) };
    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c)
}

pub fn jmp(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let target = unsafe { *pc.offset(1) as isize };
    println!("jump by: {}", target);
    let new_pc = unsafe { pc.offset(target) };
    // println!("new pc: {:?}", new_pc);
    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c)
}

pub fn jmp_if(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let cond = frame.read_bool(unsafe { *pc.offset(1) as isize });
    let target = if cond {
        unsafe { *pc.offset(2) as isize }
    } else {
        unsafe { *pc.offset(3) as isize }
    };
    // println!("jmp_if by: {}", target);
    let new_pc = unsafe { pc.offset(target) };
    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c)
}

pub fn lt_u(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let size = unsafe { *pc.offset(1) as usize };
    let r_offset = unsafe { *pc.offset(2) as isize };
    let a_offset = unsafe { *pc.offset(3) as isize };
    let b_offset = unsafe { *pc.offset(4) as isize };

    let a = frame.read_u64(a_offset);
    let b = frame.read_u64(b_offset);

    let c = (a < b) as u64;

    // println!("lt_u: {}({}) < {}({}) = {}({})", a, a_offset, b, b_offset, c, r_offset);

    frame.write_u64(r_offset, c);

    let new_pc = unsafe { pc.offset(5) };
    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c)
}

pub fn mul_f(
    pc: *const u64,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    // println!("mul_f");
    let r_offset = unsafe { *pc.offset(1) as isize };
    let a_offset = unsafe { *pc.offset(2) as isize };
    let b_offset = unsafe { *pc.offset(3) as isize };

    let a = frame.read_field(a_offset);
    let b = frame.read_field(b_offset);

    let c = a * b;

    frame.write_field(r_offset, c);

    let new_pc = unsafe { pc.offset(4) };
    dispatch(new_pc, frame, out_wit, out_a, out_b, out_c)
}

fn prepare_dispatch(program: &mut [u64]) {
    let mut current_offset = 0;
    while current_offset < program.len() {
        let opcode = program[current_offset];
        if opcode == u64::MAX {
            current_offset += 2;
            continue;
        }
        program[current_offset] = DISPATCH[opcode as usize] as u64;
        match opcode {
            0 => {
                current_offset += 3;
            }
            1 => {
                current_offset += 4;
            }
            2 => {
                current_offset += 4;
            }
            3 => {
                current_offset += 5;
            }
            4 => {
                current_offset += 5;
            }
            5 => {
                current_offset += 2;
            }
            6 => {
                current_offset += 4;
            }
            7 => {
                current_offset += 5;
            }
            8 => {
                current_offset += 4;
            }
            9 => {
                current_offset += 2;
            }
            10 => {
                current_offset += 4;
            }
            11 => {
                current_offset += 1;
            }
            12 => {
                let args_count = program[current_offset + 2] as usize;
                current_offset += 4 + 2 * args_count;
            }
            13 => {
                current_offset += 5;
            }
            14 => {
                current_offset += 1;
            }

            19 => {
                current_offset += 4;
            }
            _ => {
                panic!("Invalid opcode: {}", opcode);
            }
        }
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
