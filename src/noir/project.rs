//! Functionality for working with projects of Noir sources.

use std::any::Any;

use crate::compiler::common_subexpression_elimination::CSE;
use crate::compiler::condition_propagation::ConditionPropagation;
use crate::compiler::dead_code_elimination::DCE;
use crate::compiler::deduplicate_phis::DeduplicatePhis;
use crate::compiler::explicit_witness::ExplicitWitness;
use crate::compiler::fix_double_jumps::FixDoubleJumps;
use crate::compiler::flow_analysis::{self, FlowAnalysis};
use crate::compiler::mem2reg::Mem2Reg;
use crate::compiler::monomorphization::Monomorphization;
use crate::compiler::r1cs_gen::R1CGen;
use crate::compiler::ssa::{DefaultSsaAnnotator, SSA};
use crate::compiler::taint_analysis::TaintAnalysis;
use crate::compiler::witness_generation::WitnessGen;
use crate::noir::error::compilation::{Error as CompileError, Result as CompileResult};
use fm::FileManager;
use nargo::{
    insert_all_files_for_workspace_into_file_manager, package::Package, parse_all, prepare_package,
    workspace::Workspace,
};
use noirc_driver::{CompileOptions, check_crate};
use noirc_evaluator::ssa::ssa_gen::Ssa;
use noirc_evaluator::ssa::{SsaBuilder, SsaLogging, SsaPass};
use noirc_frontend::hir::ParsedFiles;
use noirc_frontend::monomorphization::monomorphize;

/// A manager for source files for the Noir project that we intend to extract.
#[derive(Clone)]
pub struct Project<'file_manager, 'parsed_files> {
    /// Nargo object keeping loaded files
    nargo_file_manager: &'file_manager FileManager,

    /// Nargo object keeping parsed files
    nargo_parsed_files: &'parsed_files ParsedFiles,
}

impl<'file_manager, 'parsed_files> Project<'file_manager, 'parsed_files> {
    /// Creates a new project with the provided root.
    #[allow(clippy::missing_panics_doc)]
    pub fn new(
        nargo_file_manager: &'file_manager FileManager,
        nargo_parsed_files: &'parsed_files ParsedFiles,
    ) -> Self {
        Self {
            nargo_file_manager,
            nargo_parsed_files,
        }
    }

    pub fn file_manager(&self) -> &'file_manager FileManager {
        self.nargo_file_manager
    }

    pub fn compile_package(
        &self,
        package: &Package,
        public_witness: Vec<ark_bn254::Fr>,
    ) -> CompileResult<()> {
        let (mut context, crate_id) =
            prepare_package(self.nargo_file_manager, self.nargo_parsed_files, package);
        // Enables reference tracking in the internal context.
        // context.activate_lsp_mode(); //

        // Perform compilation to check the code within it.
        let ((), _) = check_crate(
            &mut context,
            crate_id,
            &CompileOptions {
                deny_warnings: false,
                debug_comptime_in_file: None,
                ..Default::default()
            },
        )
        .map_err(|diagnostics| CompileError::CheckFailure { diagnostics })?;

        let main = context.get_main_function(context.root_crate_id()).unwrap();

        let program = monomorphize(main, &mut context.def_interner, false).unwrap();

        println!("SSA!");
        let ssa = SsaBuilder::from_program(program, SsaLogging::All, true, &None, None).unwrap();

        let passes = vec![
            // We need to get rid of function pointer parameters, otherwise they cause panic in Brillig generation.
            SsaPass::new(Ssa::defunctionalize, "Defunctionalization"),
            // Even the initial SSA generation can result in optimizations that leave a function
            // which was called in the AST not being called in the SSA. Such functions would cause
            // panics later, when we are looking for global allocations.
            SsaPass::new(
                Ssa::remove_unreachable_functions,
                "Removing Unreachable Functions",
            ),
            // We need to add an offset to constant array indices in Brillig.
            // This can change which globals are used, because constant creation might result
            // in the (re)use of otherwise unused global values.
            SsaPass::new(
                Ssa::brillig_array_get_and_set,
                "Brillig Array Get and Set Optimizations",
            ),
            // // We need a DIE pass to populate `used_globals`, otherwise it will panic later.
            SsaPass::new(
                Ssa::dead_instruction_elimination,
                "Dead Instruction Elimination",
            ),
        ];

        let ssa = ssa.run_passes(&&passes).unwrap();

        // Convert to custom SSA
        let mut custom_ssa = SSA::from_noir(&ssa.ssa);
        println!("Converted SSA Before TC:\n{}", custom_ssa.to_string(&DefaultSsaAnnotator));

        let flow_analysis = FlowAnalysis::run(&custom_ssa);
        custom_ssa.typecheck(&flow_analysis);
        println!(
            "Converted SSA:\n{}",
            custom_ssa.to_string(&DefaultSsaAnnotator)
        );

        // let flow_analysis = FlowAnalysis::run(&custom_ssa);
        // flow_analysis.save_as_png("flow_analysis.png").unwrap();

        let call_loops = flow_analysis.get_call_graph().detect_loops();
        if !call_loops.is_empty() {
            panic!(
                "Call loops detected: {:?}. We don't support recursion yet.",
                call_loops
            );
        }

        // for (func_id, cfg) in flow_analysis.function_cfgs.iter() {
        //     println!("Function {:?}:", func_id);
        //     println!("  Loop entrys: {:?}", cfg.loop_entrys);
        //     println!("  If merge points: {:?}", cfg.if_merge_points);
        // }

        // println!("test_if_body: {:?}", flow_analysis.get_if_body(FunctionId(1), BlockId(2)));

        let mut taint_analysis = TaintAnalysis::new();
        taint_analysis.run(&custom_ssa, &flow_analysis).unwrap();

        println!(
            "After taint analysis SSA:\n{}",
            custom_ssa.to_string(&taint_analysis)
        );

        let mut monomorphization = Monomorphization::new();
        monomorphization
            .run(&mut custom_ssa, &mut taint_analysis)
            .unwrap();

        println!(
            "After monomorphization SSA:\n{}",
            custom_ssa.to_string(&taint_analysis)
        );

        drop(flow_analysis); // Explicit drop to signify it's invalid now

        let flow_analysis = FlowAnalysis::run(&custom_ssa);
        // flow_analysis.save_as_png("flow_analysis_after_monomorphization.png").unwrap();

        let mut explicit_witness = ExplicitWitness::new();
        explicit_witness.run(&mut custom_ssa, &taint_analysis, &flow_analysis);

        println!(
            "After explicit witness SSA:\n{}",
            custom_ssa.to_string(&DefaultSsaAnnotator)
        );

        drop(flow_analysis);
        let flow_analysis = FlowAnalysis::run(&custom_ssa);
        let mut fix_double_jumps = FixDoubleJumps::new();
        fix_double_jumps.run(&mut custom_ssa, &flow_analysis);

        println!(
            "After fix double jumps SSA:\n{}",
            custom_ssa.to_string(&DefaultSsaAnnotator)
        );

        drop(flow_analysis);
        let flow_analysis = FlowAnalysis::run(&custom_ssa);
        custom_ssa.typecheck(&flow_analysis);

        let mut mem2reg = Mem2Reg::new();
        mem2reg.run(&mut custom_ssa, &flow_analysis);

        println!(
            "After mem2reg SSA:\n{}",
            custom_ssa.to_string(&DefaultSsaAnnotator)
        );

        let cse = CSE::new();
        cse.run(&mut custom_ssa, &flow_analysis);

        println!(
            "After CSE SSA:\n{}",
            custom_ssa.to_string(&DefaultSsaAnnotator)
        );

        let mut condition_propagation = ConditionPropagation::new();
        condition_propagation.run(&mut custom_ssa, &flow_analysis);

        println!(
            "After condition propagation SSA:\n{}",
            custom_ssa.to_string(&DefaultSsaAnnotator)
        );

        // Running a second CSE to unify spurious constants from condition propagation
        cse.run(&mut custom_ssa, &flow_analysis);

        println!(
            "After CSE SSA:\n{}",
            custom_ssa.to_string(&DefaultSsaAnnotator)
        );

        let mut deduplicate_phis = DeduplicatePhis::new();
        deduplicate_phis.run(&mut custom_ssa);

        println!(
            "After deduplicate phis SSA:\n{}",
            custom_ssa.to_string(&DefaultSsaAnnotator)
        );

        drop(flow_analysis);
        let flow_analysis = FlowAnalysis::run(&custom_ssa);

        let mut dce = DCE::new();
        dce.run(&mut custom_ssa, &flow_analysis);

        println!(
            "After DCE SSA:\n{}",
            custom_ssa.to_string(&DefaultSsaAnnotator)
        );
        drop(flow_analysis);
        let flow_analysis = FlowAnalysis::run(&custom_ssa);

        let mut fix_double_jumps = FixDoubleJumps::new();
        fix_double_jumps.run(&mut custom_ssa, &flow_analysis);

        println!(
            "After fix double jumps SSA:\n{}",
            custom_ssa.to_string(&DefaultSsaAnnotator)
        );

        drop(flow_analysis);
        let flow_analysis = FlowAnalysis::run(&custom_ssa);
        custom_ssa.typecheck(&flow_analysis);

        let mut r1cs_gen = R1CGen::new();
        r1cs_gen.run(&custom_ssa);
        let r1cs = r1cs_gen.clone().get_r1cs();
        println!(
            "R1CS (constraints = {}) (witness_size = {}):\n{}",
            r1cs.len(),
            r1cs_gen.get_witness_size(),
            r1cs.iter()
                .map(|r1c| r1c.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        );

        let mut witness_gen = WitnessGen::new(public_witness);
        witness_gen.run(&custom_ssa);
        let witness = witness_gen.get_witness();
        println!(
            "Witness:\n{}",
            witness
                .iter()
                .map(|w| w.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        println!(
            "A:\n{}",
            witness_gen
                .get_a()
                .iter()
                .map(|w| w.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        println!(
            "B:\n{}",
            witness_gen
                .get_b()
                .iter()
                .map(|w| w.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );
        println!(
            "C:\n{}",
            witness_gen
                .get_c()
                .iter()
                .map(|w| w.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        );

        r1cs_gen.verify(&witness);

        Ok(())
    }
}

// Copied from: https://github.com/noir-lang/noir/blob/e93f44cd41bbc570096e6d12c652aa4c4abc5839/tooling/nargo_cli/src/cli/compile_cmd.rs#L108
/// Parse all files in the workspace.
pub fn parse_workspace(workspace: &Workspace) -> (FileManager, ParsedFiles) {
    let mut file_manager = workspace.new_file_manager();
    insert_all_files_for_workspace_into_file_manager(workspace, &mut file_manager);
    let parsed_files = parse_all(&file_manager);
    (file_manager, parsed_files)
}
