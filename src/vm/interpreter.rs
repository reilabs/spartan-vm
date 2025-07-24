use std::{
    alloc::{self, Layout},
    marker::PhantomData,
    mem,
};

use ark_ff::{AdditiveGroup, BigInt, Fp};

use crate::compiler::Field;

const DISPATCH_SIZE: usize = 15;

type Erased = fn(&[fn(); DISPATCH_SIZE], *mut u64, *mut Frame, Frame, OutBufs);
type Handler = fn(&[Erased; DISPATCH_SIZE], *mut u64, *mut Frame, Frame, OutBufs);

const DISPATCH: [Handler; DISPATCH_SIZE] = [
    mov_const,
    add_f,
    todo,
    todo,
    todo,
    todo,
    r1c,
    todo,
    todo,
    todo,
    todo,
    ret,
    todo,
    todo,
    nop,
];

#[inline(always)]
pub fn dispatch(
    d: &[Erased; DISPATCH_SIZE],
    pc: *mut u64,
    sp: *mut Frame,
    frame: Frame,
    out: OutBufs,
) {
    let unerased: &[Handler; DISPATCH_SIZE] = unsafe { std::mem::transmute(d) };
    let opcode = unsafe { *pc };
    let handler = unsafe { *unerased.as_ptr().offset(opcode as isize) };
    handler(d, pc, sp, frame, out)
}

#[derive(Debug, Clone, Copy)]
pub struct OutBufs {
    pub witness: *mut Field,
    pub a: *mut Field,
    pub b: *mut Field,
    pub c: *mut Field,
}

impl OutBufs {
    #[inline(always)]
    pub fn write_constraint(self, a: Field, b: Field, c: Field) -> Self {
        unsafe {
            *self.a = a;
            *self.b = b;
            *self.c = c;
        }
        OutBufs {
            witness: self.witness,
            a: unsafe { self.a.offset(1) },
            b: unsafe { self.b.offset(1) },
            c: unsafe { self.c.offset(1) },
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Frame {
    size: usize,
    data: *mut u64,
}

impl Frame {
    pub fn dealloc(&self) {
        unsafe {
            alloc::dealloc(
                self.data as *mut u8,
                Layout::array::<u64>(self.size).unwrap(),
            )
        }
    }

    pub fn read_field(&self, offset: isize) -> Field {
        let a0 = unsafe { *self.data.offset(offset) };
        let a1 = unsafe { *self.data.offset(offset + 1) };
        let a2 = unsafe { *self.data.offset(offset + 2) };
        let a3 = unsafe { *self.data.offset(offset + 3) };
        Fp(BigInt([a0, a1, a2, a3]), PhantomData)
    }

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
    d: &[Erased; DISPATCH_SIZE],
    pc: *mut u64,
    sp: *mut Frame,
    frame: Frame,
    out: OutBufs,
) {
    let r_offset = unsafe { *pc.offset(1) as isize };
    let a_offset = unsafe { *pc.offset(2) as isize };
    let b_offset = unsafe { *pc.offset(3) as isize };

    let a = frame.read_field(a_offset);
    let b = frame.read_field(b_offset);

    let c = a + b;

    frame.write_field(r_offset, c);

    let new_pc = unsafe { pc.offset(4) };

    dispatch(d, new_pc, sp, frame, out)
}

pub fn ret(d: &[Erased; DISPATCH_SIZE], _pc: *mut u64, sp: *mut Frame, frame: Frame, out: OutBufs) {
    let ret_address = unsafe { mem::transmute(frame.data) };
    frame.dealloc();
    let new_sp = unsafe { sp.offset(-1) };
    let new_frame = unsafe { *new_sp };
    if new_frame.data.is_null() {
        return;
    }
    dispatch(d, ret_address, new_sp, new_frame, out)
}

pub fn todo(_d: &[Erased; DISPATCH_SIZE], _pc: *mut u64, _sp: *mut Frame, _frame: Frame, _out: OutBufs) {
    panic!("todo");
}

pub fn mov_const(
    d: &[Erased; DISPATCH_SIZE],
    pc: *mut u64,
    sp: *mut Frame,
    frame: Frame,
    out: OutBufs,
) {
    let r_offset = unsafe { *pc.offset(1) as isize };
    let val = unsafe { *pc.offset(2) };
    unsafe {
        *frame.data.offset(r_offset) = val;
    }

    let new_pc = unsafe { pc.offset(3) };
    dispatch(d, new_pc, sp, frame, out)
}

pub fn r1c(
    d: &[Erased; DISPATCH_SIZE],
    pc: *mut u64,
    sp: *mut Frame,
    frame: Frame,
    out: OutBufs,
) {
    let a_offset = unsafe { *pc.offset(1) as isize };
    let b_offset = unsafe { *pc.offset(2) as isize };
    let c_offset = unsafe { *pc.offset(3) as isize };

    let a = frame.read_field(a_offset);
    let b = frame.read_field(b_offset);
    let c = frame.read_field(c_offset);

    let out = out.write_constraint(a, b, c);

    let new_pc = unsafe { pc.offset(4) };
    dispatch(d, new_pc, sp, frame, out)
}

pub fn nop(d: &[Erased; DISPATCH_SIZE], pc: *mut u64, sp: *mut Frame, frame: Frame, out: OutBufs) {
    let new_pc = unsafe { pc.offset(1) };
    dispatch(d, new_pc, sp, frame, out)
}

// #[instrument(skip_all, name = "Interpreter::run")]
pub fn run_interpreter(
    program: &mut [u64],
    inputs: &[Field],
) -> (Vec<Field>, Vec<Field>, Vec<Field>, Vec<Field>) {
    let mut stack = vec![
        Frame {
            size: 0,
            data: std::ptr::null_mut()
        };
        10
    ];
    let first_frame_contents: *mut u64 =
        unsafe { alloc::alloc(Layout::array::<u64>(program[0] as usize).unwrap()) as *mut u64 };
    for (i, el) in inputs.iter().enumerate() {
        unsafe {
            *first_frame_contents.offset(2 + (i as isize) * 4) = el.0.0[0];
            *first_frame_contents.offset(2 + (i as isize) * 4 + 1) = el.0.0[1];
            *first_frame_contents.offset(2 + (i as isize) * 4 + 2) = el.0.0[2];
            *first_frame_contents.offset(2 + (i as isize) * 4 + 3) = el.0.0[3];
        }
    }
    stack[1] = Frame {
        size: program[0] as usize,
        data: first_frame_contents,
    };
    let sp = unsafe { stack.as_mut_ptr().offset(1) };

    let pc = unsafe { program.as_mut_ptr().offset(1) };

    let mut out_wit = vec![Field::ZERO; 10];
    let mut out_a = vec![Field::ZERO; 10];
    let mut out_b = vec![Field::ZERO; 10];
    let mut out_c = vec![Field::ZERO; 10];

    let out = OutBufs {
        witness: out_wit.as_mut_ptr(),
        a: out_a.as_mut_ptr(),
        b: out_b.as_mut_ptr(),
        c: out_c.as_mut_ptr(),
    };

    let erased: &[Erased; 15] = unsafe { mem::transmute(&DISPATCH) };

    dispatch(erased, pc, sp, stack[1], out);

    (out_wit, out_a, out_b, out_c)
}
