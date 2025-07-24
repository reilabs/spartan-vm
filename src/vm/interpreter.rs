use std::{
    alloc::{self, Layout},
    marker::PhantomData,
    mem,
};

use ark_ff::{AdditiveGroup, BigInt, Fp};
use tracing::instrument;

use crate::compiler::Field;

const DISPATCH_SIZE: usize = 15;

type Handler = fn(
    *const u64,
    *mut Frame,
    Frame,
    *mut Field,
    *mut Field,
    *mut Field,
    *mut Field,
);

const DISPATCH: [Handler; DISPATCH_SIZE] = [
    mov_const, add_f, todo, todo, todo, todo, r1c, todo, todo, todo, todo, ret, todo, todo, nop,
];

#[inline(always)]
pub fn dispatch(
    pc: *const u64,
    sp: *mut Frame,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let opcode: Handler = unsafe { mem::transmute::<_, _>(*pc) };
    opcode(pc, sp, frame, out_wit, out_a, out_b, out_c);
}

#[derive(Debug, Copy, Clone)]
pub struct Frame {
    data: *mut u64,
}

impl Frame {
    pub fn alloc(size: u64) -> Self {
        unsafe {
            let layout = Layout::array::<u64>(size as usize + 1).unwrap();
            let data = alloc::alloc(layout) as *mut u64;
            *data = size;
            let data = data.offset(1);
            Frame { data }
        }
    }

    pub fn dealloc(&self) {
        unsafe {
            let real_data = self.data.offset(-1);
            let size = *real_data;
            alloc::dealloc(
                real_data as *mut u8,
                Layout::array::<u64>(size as usize + 1).unwrap(),
            )
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
}

pub fn add_f(
    pc: *const u64,
    sp: *mut Frame,
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

    dispatch(new_pc, sp, frame, out_wit, out_a, out_b, out_c)
}

pub fn ret(
    _pc: *const u64,
    sp: *mut Frame,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let ret_address = unsafe { *frame.data } as *mut u64;
    frame.dealloc();
    let new_sp = unsafe { sp.offset(-1) };
    let new_frame = unsafe { *new_sp };
    if new_frame.data.is_null() {
        return;
    }
    dispatch(
        ret_address,
        new_sp,
        new_frame,
        out_wit,
        out_a,
        out_b,
        out_c,
    )
}

pub fn todo(
    _pc: *const u64,
    _sp: *mut Frame,
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
    sp: *mut Frame,
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
    dispatch(new_pc, sp, frame, out_wit, out_a, out_b, out_c)
}

pub fn r1c(
    pc: *const u64,
    sp: *mut Frame,
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
    dispatch(new_pc, sp, frame, out_wit, out_a, out_b, out_c);
}

pub fn nop(
    pc: *const u64,
    sp: *mut Frame,
    frame: Frame,
    out_wit: *mut Field,
    out_a: *mut Field,
    out_b: *mut Field,
    out_c: *mut Field,
) {
    let new_pc = unsafe { pc.offset(1) };
    dispatch(new_pc, sp, frame, out_wit, out_a, out_b, out_c)
}

fn prepare_dispatch(program: &mut [u64], dispatch: &[Handler]) {
    let mut current_offset = 1;
    while current_offset < program.len() {
        let opcode = program[current_offset];
        program[current_offset] = dispatch[opcode as usize] as u64;
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
                current_offset += 3;
            }
            10 => {
                current_offset += 4;
            }
            11 => {
                current_offset += 1;
            }
            12 => {
                todo!();
            }
            13 => {
                current_offset += 5;
            }
            14 => {
                current_offset += 1;
            }
            _ => {
                panic!("Invalid opcode: {}", opcode);
            }
        }
    }
}

#[instrument(skip_all, name = "Interpreter::run")]
pub fn run_interpreter(
    program: &[u64],
    inputs: &[Field],
) -> (Vec<Field>, Vec<Field>, Vec<Field>, Vec<Field>) {
    let mut stack = vec![
        Frame {
            data: std::ptr::null_mut()
        };
        10
    ];
    stack[1] = Frame::alloc(program[0]);
    for (i, el) in inputs.iter().enumerate() {
        stack[1].write_field(2 + (i as isize) * 4, *el);
    }

    let sp = unsafe { stack.as_mut_ptr().offset(1) };

    let mut program = program.to_vec();
    // let mut dispatch_table = DISPATCH;
    let dispatch_table = &DISPATCH;
    prepare_dispatch(&mut program, dispatch_table);

    let pc = unsafe { program.as_mut_ptr().offset(1) };

    let mut out_wit = vec![Field::ZERO; 10];
    let mut out_a = vec![Field::ZERO; 10];
    let mut out_b = vec![Field::ZERO; 10];
    let mut out_c = vec![Field::ZERO; 10];

    dispatch(
        pc,
        sp,
        stack[1],
        out_wit.as_mut_ptr(),
        out_a.as_mut_ptr(),
        out_b.as_mut_ptr(),
        out_c.as_mut_ptr(),
    );

    (out_wit, out_a, out_b, out_c)
}
