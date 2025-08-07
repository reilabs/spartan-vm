#![allow(unused_variables)]

use crate::vm::interpreter::dispatch;
use opcode_gen::interpreter;

use crate::{compiler::Field, vm::interpreter::{Frame, Handler}};

use std::fmt::Display;

pub const LIMBS: usize = 4;

pub struct FramePosition(pub usize);

impl FramePosition {
    pub fn offset(&self, offset: isize) -> FramePosition {
        FramePosition(self.0.checked_add_signed(offset).unwrap())
    }
    pub fn return_data_ptr() -> FramePosition {
        FramePosition(0)
    }
    pub fn return_address_ptr() -> FramePosition {
        FramePosition(1)
    }
}

pub struct JumpTarget(pub isize);

#[interpreter]
mod def {

    #[raw_opcode]
    fn jmp(
        pc: *const u64,
        frame: Frame,
        out_wit: *mut Field,
        out_a: *mut Field,
        out_b: *mut Field,
        out_c: *mut Field,
        target: JumpTarget,
    ) {
        let pc = unsafe { pc.offset(target.0) };
        dispatch(pc, frame, out_wit, out_a, out_b, out_c);
    }

    #[raw_opcode]
    fn jmp_if(
        pc: *const u64,
        frame: Frame,
        out_wit: *mut Field,
        out_a: *mut Field,
        out_b: *mut Field,
        out_c: *mut Field,
        #[frame] cond: u64,
        if_t: JumpTarget,
        if_f: JumpTarget,
    ) {
        let target = if cond != 0 {
            if_t
        } else {
            if_f
        };
        let pc = unsafe { pc.offset(target.0) };
        dispatch(pc, frame, out_wit, out_a, out_b, out_c);
    }

    #[raw_opcode]
    fn call(
        pc: *const u64,
        frame: Frame,
        out_wit: *mut Field,
        out_a: *mut Field,
        out_b: *mut Field,
        out_c: *mut Field,
        func: JumpTarget,
        args: &[(usize, FramePosition)],
        ret: FramePosition,
    ) {
        todo!()
    }

    #[raw_opcode]
    fn ret(
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
        dispatch(ret_address, new_frame, out_wit, out_a, out_b, out_c);
    }

    #[raw_opcode]
    fn r1c(
        pc: *const u64,
        frame: Frame,
        out_wit: *mut Field,
        out_a: *mut Field,
        out_b: *mut Field,
        out_c: *mut Field,
        #[frame] a: Field,
        #[frame] b: Field,
        #[frame] c: Field,
    ) {
        unsafe {
            *out_a = a;
            *out_b = b;
            *out_c = c;
        }

        let out_a = unsafe { out_a.offset(1) };
        let out_b = unsafe { out_b.offset(1) };
        let out_c = unsafe { out_c.offset(1) };
        let pc = unsafe { pc.offset(4) };
        dispatch(pc, frame, out_wit, out_a, out_b, out_c);
    }

    #[raw_opcode]
    fn write_witness(
        pc: *const u64,
        frame: Frame,
        out_wit: *mut Field,
        out_a: *mut Field,
        out_b: *mut Field,
        out_c: *mut Field,
        #[frame] val: Field,
    ) {
        unsafe {
            *out_wit = val;
        }
        let out_wit = unsafe { out_wit.offset(1) };
        let pc = unsafe { pc.offset(2) };
        dispatch(pc, frame, out_wit, out_a, out_b, out_c);
    }

    #[opcode]
    fn nop() {}

    #[opcode]
    fn mov_const(#[out] res: *mut u64, val: u64) {
        unsafe {
            *res = val;
        }
    }

    #[opcode]
    fn mov_frame(frame: Frame, target: FramePosition, source: FramePosition, size: usize) {
        frame.memcpy(target.0 as isize, source.0 as isize, size);
    }

    #[opcode]
    fn write_ptr(frame: Frame, ptr: FramePosition, offset: isize, src: FramePosition, size: usize) {
        todo!()
    }

    #[opcode]
    fn add_u64(#[out] res: *mut u64, #[frame] a: u64, #[frame] b: u64) {
        unsafe {
            *res = a + b;
        }
    }

    #[opcode]
    fn sub_u64(#[out] res: *mut u64, #[frame] a: u64, #[frame] b: u64) {
        unsafe {
            *res = a - b;
        }
    }

    #[opcode]
    fn div_u64(#[out] res: *mut u64, #[frame] a: u64, #[frame] b: u64) {
        unsafe {
            *res = a / b;
        }
    }

    #[opcode]
    fn mul_u64(#[out] res: *mut u64, #[frame] a: u64, #[frame] b: u64) {
        unsafe {
            *res = a * b;
        }
    }

    #[opcode]
    fn and_u64(#[out] res: *mut u64, #[frame] a: u64, #[frame] b: u64) {
        unsafe {
            *res = a & b;
        }
    }

    #[opcode]
    fn not_u64(#[out] res: *mut u64, #[frame] a: u64) {
        unsafe {
            *res = !a;
        }
    }

    #[opcode]
    fn eq_u64(#[out] res: *mut u64, #[frame] a: u64, #[frame] b: u64) {
        unsafe {
            *res = (a == b) as u64;
        }
    }

    #[opcode]
    fn lt_u64(#[out] res: *mut u64, #[frame] a: u64, #[frame] b: u64) {
        unsafe {
            *res = (a < b) as u64;
        }
    }

    #[opcode]
    fn truncate_u64(#[out] res: *mut u64, #[frame] a: u64, to_bits: u64) {
        todo!()
    }

    #[opcode]
    fn truncate_f_to_u(#[out] res: *mut u64, #[frame] a: Field, to_bits: u64) {
        todo!()
    }

    #[opcode]
    fn add_field(#[out] res: *mut Field, #[frame] a: Field, #[frame] b: Field) {
        unsafe {
            *res = a + b;
        }
    }

    #[opcode]
    fn sub_field(#[out] res: *mut Field, #[frame] a: Field, #[frame] b: Field) {
        unsafe {
            *res = a - b;
        }
    }

    #[opcode]
    fn div_field(#[out] res: *mut Field, #[frame] a: Field, #[frame] b: Field) {
        unsafe {
            *res = a / b;
        }
    }

    #[opcode]
    fn mul_field(#[out] res: *mut Field, #[frame] a: Field, #[frame] b: Field) {
        unsafe {
            *res = a * b;
        }
    }
}

pub struct Function {
    pub name: String,
    pub frame_size: usize,
    pub code: Vec<OpCode>,
}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "fn {} (frame_size = {}):", self.name, self.frame_size)?;
        for op in &self.code {
            writeln!(f, "  {}", op)?;
        }
        Ok(())
    }
}

pub struct Program {
    pub functions: Vec<Function>,
}

impl Display for Program {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let max_line_number: usize = self.functions.iter().map(|f| f.code.len()).sum::<usize>() - 1;
        let max_line_number_digits = max_line_number.to_string().len();
        let max_function_idx = self.functions.len().to_string().len() - 1;
        let max_function_idx_digits = max_function_idx.to_string().len();
        let mut line = 0;
        for (i, function) in self.functions.iter().enumerate() {
            writeln!(
                f,
                "{: >max_function_idx_digits$}: fn {} (frame_size = {})",
                i, function.name, function.frame_size
            )?;
            for op in &function.code {
                writeln!(f, "  {: >max_line_number_digits$}: {}", line, op)?;
                line += 1;
            }
        }
        Ok(())
    }
}

impl Program {
    pub fn to_binary(&self) -> Vec<u64> {
        let mut binary = Vec::new();
        let mut positions = vec![];
        let mut jumps_to_fix: Vec<(usize, isize)> = vec![];

        for function in &self.functions {
            // Function marker
            binary.push(u64::MAX);
            binary.push(function.frame_size as u64);

            for op in &function.code {
                positions.push(binary.len());
                op.to_binary(&mut binary, &mut jumps_to_fix);
            }
        }
        for (jump_position, add_offset) in jumps_to_fix {
            let target = binary[jump_position];
            let target_pos = positions[target as usize];
            binary[jump_position] =
                (target_pos as isize - (jump_position as isize + add_offset)) as u64;
        }
        binary
    }
}
