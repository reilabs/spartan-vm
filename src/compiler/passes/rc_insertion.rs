use tracing::{Level, instrument};

use crate::compiler::{
    analysis::liveness::{FunctionLiveness, LivenessAnalysis},
    flow_analysis::CFG,
    pass_manager::{DataPoint, Pass, PassInfo, PassManager},
    ssa::{Function, Terminator, SSA},
};

pub struct RCInsertion {}

impl<V: Clone> Pass<V> for RCInsertion {
    fn pass_info(&self) -> PassInfo {
        PassInfo {
            name: "RCInsertion",
            invalidates: vec![DataPoint::CFG],
            needs: vec![DataPoint::CFG, DataPoint::Types],
        }
    }

    fn run(&self, ssa: &mut SSA<V>, pass_manager: &PassManager<V>) {
        let cfg = pass_manager.get_cfg();

        let liveness = LivenessAnalysis::new().run(ssa, cfg);

        for (function_id, function) in ssa.iter_functions_mut() {
            let cfg = cfg.get_function_cfg(*function_id);
            let liveness = &liveness.function_liveness[function_id];
            self.run_function(function, cfg, &liveness);
        }
    }
}

impl RCInsertion {
    pub fn new() -> Self {
        Self {}
    }

    #[instrument(skip_all, level = Level::DEBUG, name = "RCInsertion::run_function", fields(function = function.get_name()))]
    pub fn run_function<V: Clone>(
        &self,
        function: &mut Function<V>,
        cfg: &CFG,
        liveness: &FunctionLiveness,
    ) {
        for (block_id, block) in function.get_blocks_mut() {

            // We're traversing the block backwards, dropping everything that's not live
            // after the currently visited instruction.
            // This means new_instructions will be reversed, so some care is needed when
            // inserting drops.
            // let mut currently_live = liveness.block_liveness[block_id].live_out.clone();
            // let mut new_instructions = vec![];

            // match block.get_terminator().unwrap() {
            //     Terminator::Return(values) => {
            //         // We don't drop these values.
            //         // The caller will be responsible for them.
            //         currently_live.extend(values);
            //     }
            //     Terminator::Jmp(_, values) => {
            //         for value in values {
            //             // Values that die here, are passed without an increase 
            //         }
            //     }
            // }


        }
    }
}
