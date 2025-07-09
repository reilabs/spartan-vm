use crate::compiler::{ssa::{FunctionId, SSA}, taint_analysis::{Taint, TaintAnalysis}};

struct WorkItem {
    function_id: FunctionId,
    target_function_id: FunctionId,
    cfg_taint: Taint,
    param_taints: Vec<Taint>,
    return_taints: Vec<Taint>,
}

pub struct Monomorphization {

}

impl Monomorphization {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(&self, ssa: &mut SSA, taint_analysis: &mut TaintAnalysis) -> Result<(), String> {
        let entry_point = ssa.get_main_id();
        let entry_point_taint = taint_analysis.get_function_taint(entry_point);
        Ok(())

        // let mut constraint_solver = ConstraintSolver::new(&entry_point_taint);
        // constraint_solver.add_assumption(
        //     &TaintType::Primitive(entry_point_taint.cfg_taint.clone()),
        //     &TaintType::Primitive(Taint::Pure),
        // );
    }
}