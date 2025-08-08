#![allow(unused_variables)]

use crate::vm::interpreter::dispatch;
use opcode_gen::interpreter;

use crate::vm::array::{Array, ArrayMeta};
use crate::{
    compiler::Field,
    vm::interpreter::{Frame, Handler},
};

use std::fmt::Display;
use std::{mem, ptr};

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
        // println!("jmp: target={:?}", pc);
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
        let target = if cond != 0 { if_t } else { if_f };
        let pc = unsafe { pc.offset(target.0) };
        // println!("jmp_if: cond={} target={:?}", cond, pc);
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
        let func_pc = unsafe { pc.offset(func.0) };
        let func_frame_size = unsafe { *func_pc.offset(-1) };
        let new_frame = Frame::push(func_frame_size, frame);
        let ret_data_ptr = unsafe { frame.data.offset(ret.0 as isize) };
        let ret_pc = unsafe { pc.offset(4 + 2 * args.len() as isize) };

        unsafe {
            *new_frame.data = ret_data_ptr as u64;
            *new_frame.data.offset(1) = ret_pc as u64;
        };

        let mut current_child = unsafe { new_frame.data.offset(2) };

        for (i, (arg_size, arg_pos)) in args.iter().enumerate() {
            frame.write_to(current_child, arg_pos.0 as isize, *arg_size);
            current_child = unsafe { current_child.offset(*arg_size as isize) };
        }

        // println!("call: func={:?} (size={})", func_pc, unsafe {*func_pc.offset(-1)});

        dispatch(func_pc, new_frame, out_wit, out_a, out_b, out_c);
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
            // println!("finish return");
            return;
        }
        // println!("ret");
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

        // println!("r1cs");

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
    fn write_ptr(
        frame: Frame,
        #[frame] ptr: *mut u64,
        offset: isize,
        src: FramePosition,
        size: usize,
    ) {
        let ptr = unsafe { ptr.offset(offset) };
        frame.write_to(ptr, src.0 as isize, size);
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
        unsafe {
            *res = a & ((1 << to_bits) - 1);
        }
    }

    #[opcode]
    fn truncate_f_to_u(#[out] res: *mut Field, #[frame] a: Field, to_bits: u64) {
        unsafe {
            *res = From::from(ark_ff::PrimeField::into_bigint(a).0[0] & ((1 << to_bits) - 1));
        }
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

    #[opcode]
    fn cast_field_to_u64(#[out] res: *mut u64, #[frame] a: Field) {
        unsafe {
            *res = ark_ff::PrimeField::into_bigint(a).0[0];
        }
    }

    #[opcode]
    fn cast_u64_to_field(#[out] res: *mut Field, #[frame] a: u64) {
        unsafe {
            *res = From::from(a);
        }
    }

    #[opcode]
    fn array_alloc(
        #[out] res: *mut Array,
        stride: usize,
        meta: ArrayMeta,
        items: &[FramePosition],
        frame: Frame,
    ) {
        let array = Array::alloc(meta);
        // println!(
        //     "array_alloc: size={} stride={} has_ptr_elems={} @ {:?}",
        //     meta.size(),
        //     stride,
        //     meta.ptr_elems(),
        //     array.0
        // );
        for (i, item) in items.iter().enumerate() {
            let tgt = array.idx(i, stride);
            frame.write_to(tgt, item.0 as isize, stride);
        }
        unsafe {
            *res = array;
        }
    }

    #[opcode]
    fn array_get(#[out] res: *mut u64, #[frame] array: Array, #[frame] index: u64, stride: usize) {
        let src = array.idx(index as usize, stride);
        unsafe {
            ptr::copy_nonoverlapping(src, res, stride);
        }
    }

    #[opcode]
    fn array_set(
        #[out] res: *mut Array,
        #[frame] array: Array,
        #[frame] index: u64,
        source: FramePosition,
        stride: usize,
        frame: Frame,
    ) {
        let new_array = array.copy_if_reused();
        let target = new_array.idx(index as usize, stride);
        frame.write_to(target, source.0 as isize, stride);
        unsafe {
            *res = new_array;
        }
        // println!("arr_set_outro");
    }

    #[opcode]
    fn inc_array_rc(#[frame] array: Array, amount: u64) {
        // println!("inc_array_rc_intro");
        array.inc_rc(amount);
        // println!("inc_array_rc_outro");
    }

    #[opcode]
    fn dec_array_rc(#[frame] array: Array) {
        // println!("dec_array_rc_intro");
        array.dec_rc();
        // println!("dec_array_rc_outro");
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
