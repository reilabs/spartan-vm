use std::fmt::Display;

pub const LIMBS: usize = 4;

pub struct FramePosition(pub usize);

impl FramePosition {
    pub fn offset(&self, offset: isize) -> FramePosition {
        FramePosition(self.0.checked_add_signed(offset).unwrap())
    }
    pub fn return_data_ptr() -> FramePosition {
        FramePosition(1)
    }
}

pub struct JumpTarget(pub isize);

pub enum OpCode {
    Const(FramePosition, u64),
    AddF(FramePosition, FramePosition, FramePosition),
    MulF(FramePosition, FramePosition, FramePosition),
    AddU(usize, FramePosition, FramePosition, FramePosition),
    LtU(usize, FramePosition, FramePosition, FramePosition),
    WriteWitness(FramePosition),
    ConstraintR1C(FramePosition, FramePosition, FramePosition),
    Select(FramePosition, FramePosition, FramePosition, FramePosition),
    Mov(FramePosition, FramePosition, usize),
    Jmp(JumpTarget),
    JmpIf(FramePosition, JumpTarget, JumpTarget),
    Return,
    Call(JumpTarget, Vec<FramePosition>, FramePosition),
    WritePtr(FramePosition, isize, FramePosition, usize),
    Nop,
}

impl Display for OpCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OpCode::Const(pos, val) => write!(f, "mov %{} {}", pos.0, val),
            OpCode::AddF(pos1, pos2, pos3) => {
                write!(f, "f_add %{} %{} %{}", pos1.0, pos2.0, pos3.0)
            }
            OpCode::MulF(pos1, pos2, pos3) => {
                write!(f, "f_mul %{} %{} %{}", pos1.0, pos2.0, pos3.0)
            }
            OpCode::AddU(size, pos1, pos2, pos3) => {
                write!(f, "u_add({}) %{} %{} %{}", size, pos1.0, pos2.0, pos3.0)
            }
            OpCode::LtU(size, pos1, pos2, pos3) => {
                write!(f, "u_lt({}) %{} %{} %{}", size, pos1.0, pos2.0, pos3.0)
            }
            OpCode::WriteWitness(pos) => write!(f, "write_witness %{}", pos.0),
            OpCode::ConstraintR1C(pos1, pos2, pos3) => {
                write!(f, "r1c_constraint %{} %{} %{}", pos1.0, pos2.0, pos3.0)
            }
            OpCode::Select(pos1, pos2, pos3, pos4) => {
                write!(f, "select %{} %{} %{} %{}", pos1.0, pos2.0, pos3.0, pos4.0)
            }
            OpCode::Mov(pos1, pos2, size) => write!(f, "mov({}) %{} %{}", size, pos1.0, pos2.0),
            OpCode::WritePtr(tgt, offset, val, size) => {
                let sign = if *offset < 0 { "-" } else { "+" };
                write!(f, "mov({}) [%{}{}{}] %{}", size, tgt.0, sign, offset.abs(), val.0)
            }
            OpCode::Jmp(target) => write!(f, "jmp {}\n", target.0),
            OpCode::JmpIf(pos, target1, target2) => {
                write!(f, "jmp_if %{} {} {}\n", pos.0, target1.0, target2.0)
            }
            OpCode::Return => write!(f, "return\n"),
            OpCode::Call(target, args, ret) => write!(
                f,
                "call {} [{}] %{}",
                target.0,
                args.iter()
                    .map(|a| format!("%{}", a.0))
                    .collect::<Vec<_>>()
                    .join(", "),
                ret.0
            ),
            OpCode::Nop => write!(f, "nop"),
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
            writeln!(f, "{: >max_function_idx_digits$}: fn {}", i, function.name)?;
            for op in &function.code {
                writeln!(f, "  {: >max_line_number_digits$}: {}", line, op)?;
                line += 1;
            }
        }
        Ok(())
    }
}
