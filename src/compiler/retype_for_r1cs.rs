use crate::compiler::taint_analysis::ConstantTaint;

pub struct RetypeForR1CS {}

impl RetypeForR1CS {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(&self, ssa: crate::compiler::ssa::SSA<ConstantTaint>) -> crate::compiler::ssa::SSA<()> {
    }
}
