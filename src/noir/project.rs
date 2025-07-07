//! Functionality for working with projects of Noir sources.

use crate::{compiler::flow_analysis::FlowAnalysis, noir::{
    error::compilation::{Error as CompileError, Result as CompileResult}, WithWarnings
}};
use fm::FileManager;
use nargo::{
    insert_all_files_for_workspace_into_file_manager, package::Package, parse_all, prepare_package,
    workspace::Workspace,
};
use noirc_driver::{CompileOptions, check_crate};
use noirc_evaluator::ssa::{minimal_passes, SsaBuilder, SsaEvaluatorOptions, SsaLogging};
use noirc_frontend::hir::ParsedFiles;
use noirc_frontend::monomorphization::monomorphize;
use crate::compiler::ssa::SSA;

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

    /// Takes the project definition and performs compilation of that project to
    /// the Noir intermediate representation for further analysis and the
    /// emission of Lean code.
    ///
    /// If the compilation process generates non-fatal warnings, these are
    /// attached to the return value.
    ///
    /// # Errors
    ///
    /// - [`CompileError`] if the compilation process fails.
    pub fn compile_package(&self, package: &Package) -> CompileResult<()> {
        let (mut context, crate_id) =
            prepare_package(self.nargo_file_manager, self.nargo_parsed_files, package);
        // Enables reference tracking in the internal context.
        // context.activate_lsp_mode(); //

        // Perform compilation to check the code within it.
        let ((), warnings) = check_crate(
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

        // let options = SsaEvaluatorOptions {
        //     ssa_logging: SsaLogging::None,
        //     brillig_options: Default::default(),
        //     print_codegen_timings: false,
        //     expression_width: Default::default(),
        //     emit_ssa: None,
        //     skip_underconstrained_check: false,
        //     skip_brillig_constraints_check: false,
        //     enable_brillig_constraints_check_lookback: false,
        //     inliner_aggressiveness: 0,
        //     max_bytecode_increase_percent: None,
        //     skip_passes: vec![],
        // };

        println!("SSA!");
        let ssa = SsaBuilder::from_program(program, SsaLogging::All, true, &None, None).unwrap();
        let ssa = ssa.run_passes(&minimal_passes()).unwrap();

        // Convert to custom SSA
        let mut custom_ssa = SSA::from_noir(&ssa.ssa);
        custom_ssa.typecheck();
        println!("Converted SSA:\n{}", custom_ssa.to_string(|_, _, _| "".to_string()));

        let mut flow_analysis = FlowAnalysis::new();
        flow_analysis.run(&custom_ssa);
        flow_analysis.save_as_png("flow_analysis.png").unwrap();

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
