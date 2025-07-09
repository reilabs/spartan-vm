//! Functionality for working with projects of Noir sources.

use std::rc::Rc;

use crate::compiler::ssa::{DefaultSsaAnnotator, SSA};
use crate::compiler::taint_analysis::{ConstantTaint, Taint, TaintType};
use crate::{
    compiler::{
        constraint_solver::ConstraintSolver, flow_analysis::FlowAnalysis, ssa::FunctionId,
        taint_analysis::TaintAnalysis,
    },
    noir::error::compilation::{Error as CompileError, Result as CompileResult},
};
use fm::FileManager;
use nargo::{
    insert_all_files_for_workspace_into_file_manager, package::Package, parse_all, prepare_package,
    workspace::Workspace,
};
use noirc_driver::{CompileOptions, check_crate};
use noirc_evaluator::ssa::{SsaBuilder, SsaLogging, minimal_passes};
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

    pub fn compile_package(&self, package: &Package) -> CompileResult<()> {
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
        let ssa = ssa.run_passes(&minimal_passes()).unwrap();

        // Convert to custom SSA
        let mut custom_ssa = SSA::from_noir(&ssa.ssa);
        custom_ssa.typecheck();
        println!(
            "Converted SSA:\n{}",
            custom_ssa.to_string(&DefaultSsaAnnotator)
        );

        let mut flow_analysis = FlowAnalysis::new();
        flow_analysis.run(&custom_ssa);
        flow_analysis.save_as_png("flow_analysis.png").unwrap();

        let call_loops = flow_analysis.detect_call_loops();
        if !call_loops.is_empty() {
            panic!(
                "Call loops detected: {:?}. We don't support recursion yet.",
                call_loops
            );
        }

        for (func_id, cfg) in flow_analysis.function_cfgs.iter() {
            println!("Function {:?}:", func_id);
            println!("  Loop entrys: {:?}", cfg.loop_entrys);
            println!("  If merge points: {:?}", cfg.if_merge_points);
        }

        let mut taint_analysis = TaintAnalysis::new();
        taint_analysis.run(&custom_ssa, &flow_analysis).unwrap();

        println!(
            "After taint analysis SSA:\n{}",
            custom_ssa.to_string(&taint_analysis)
        );

        let mut constraint_solver =
            ConstraintSolver::new(&taint_analysis.get_function_taint(custom_ssa.get_main_id()));

        let main_func = taint_analysis.get_function_taint(custom_ssa.get_main_id());
        constraint_solver.add_assumption(
            &TaintType::Primitive(main_func.cfg_taint.clone()),
            &TaintType::Primitive(Taint::Constant(ConstantTaint::Pure)),
        );
        for param in main_func.parameters.iter() {
            constraint_solver.add_assumption(param, &mainify_taint(param));
        }

        constraint_solver.solve();

        let cloned_main = main_func.update_from_unification(&constraint_solver.unification);

        println!(
            "Monomorphized SSA:\n{}",
            custom_ssa
                .get_main()
                .to_string(custom_ssa.get_main_id(), &cloned_main)
        );
        // println!("Taint analysis:\n{}", taint_analysis.to_string());

        let big_function_id = FunctionId(1);
        let big_function_taint = taint_analysis.get_function_taint(big_function_id);

        let mut constraint_solver = ConstraintSolver::new(&big_function_taint);
        constraint_solver.add_assumption(
            &TaintType::Primitive(big_function_taint.cfg_taint.clone()),
            &TaintType::Primitive(Taint::Constant(ConstantTaint::Pure)),
        );
        for param in big_function_taint.parameters.iter() {
            constraint_solver.add_assumption(param, &mainify_taint(param));
        }
        constraint_solver.add_assumption(
            &big_function_taint.returns_taint[0],
            &TaintType::Primitive(Taint::Constant(ConstantTaint::Witness)),
        );
        constraint_solver.solve();

        let big_function_taint =
            big_function_taint.update_from_unification(&constraint_solver.unification);
        println!(
            "Monomorphized SSA:\n{}",
            custom_ssa
                .get_function(big_function_id)
                .to_string(big_function_id, &big_function_taint)
        );

        Ok(())
    }
}

pub fn mainify_taint(taint: &TaintType) -> TaintType {
    match taint {
        TaintType::Primitive(_) => TaintType::Primitive(Taint::Constant(ConstantTaint::Witness)),
        TaintType::NestedImmutable(_, inner) => {
            TaintType::NestedImmutable(Taint::Constant(ConstantTaint::Pure), Box::new(mainify_taint(inner)))
        }
        _ => panic!("Cannot mainify taint: {:?}", taint),
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
