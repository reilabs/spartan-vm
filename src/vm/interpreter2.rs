use crate::vm::bytecode::{FramePosition, JumpTarget};
use crate::vm::interpreter::dispatch;
use opcode_gen::interpreter;

use crate::{compiler::Field, vm::interpreter::Frame};

#[interpreter]
mod def {
    #[opcode]
    fn add_u64(#[out] res: *mut u64, #[frame] a: u64, #[frame] b: u64) {
        unsafe {
            *res = a + b;
        }
    }

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
        todo!()
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
}
