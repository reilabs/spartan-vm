use std::{fmt::Display, fs, path::PathBuf};

use crate::compiler::{flow_analysis::FlowAnalysis, ir::r#type::CommutativeMonoid, ssa::SSA};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DataPoint {
    CFG,
    Types,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PassInfo {
    pub name: &'static str,
    pub invalidates: Vec<DataPoint>,
    pub needs: Vec<DataPoint>,
}

pub trait Pass<V> {
    fn run(&self, ssa: &mut SSA<V>, pass_manager: &PassManager<V>);
    fn pass_info(&self) -> PassInfo;
}

pub struct PassManager<V> {
    passes: Vec<Box<dyn Pass<V>>>,
    current_pass_info: Option<PassInfo>,
    cfg: Option<FlowAnalysis>,
    types_valid: bool,
    debug_output_dir: Option<PathBuf>,
}

impl<V: Clone + CommutativeMonoid + Eq + Display> PassManager<V> {
    pub fn new(passes: Vec<Box<dyn Pass<V>>>) -> Self {
        Self {
            passes,
            current_pass_info: None,
            cfg: None,
            types_valid: false,
            debug_output_dir: None,
        }
    }

    pub fn set_debug_output_dir(&mut self, debug_output_dir: PathBuf) {
        self.debug_output_dir = Some(debug_output_dir);
    }

    #[tracing::instrument(skip_all, name = "PassManager::run")]
    pub fn run(&mut self, ssa: &mut SSA<V>) {
        if let Some(debug_output_dir) = &self.debug_output_dir {
            if debug_output_dir.exists() {
                fs::remove_dir_all(&debug_output_dir).unwrap();
            }
            fs::create_dir(&debug_output_dir).unwrap();
        }

        let passes = std::mem::take(&mut self.passes);
        for (i, pass) in passes.iter().enumerate() {
            self.run_pass(ssa, pass.as_ref(), i);
        }
        self.passes = passes;
        self.output_final_debug_info(ssa);
    }

    #[tracing::instrument(skip_all, fields(pass = %pass.pass_info().name))]
    fn run_pass(&mut self, ssa: &mut SSA<V>, pass: &dyn Pass<V>, pass_index: usize) {
        self.initialize_pass_data(ssa, &pass.pass_info());
        self.output_debug_info(ssa, pass_index, &pass.pass_info());
        self.current_pass_info = Some(pass.pass_info());
        pass.run(ssa, self);
        self.tear_down_pass_data(&pass.pass_info());
    }

    fn output_debug_info(&mut self, ssa: &SSA<V>, pass_index: usize, pass_info: &PassInfo) {
        let Some(debug_output_dir) = &self.debug_output_dir else {
            return;
        };
        if pass_info.needs.contains(&DataPoint::CFG) {
            if let Some(cfg) = &self.cfg {
                cfg.generate_images(
                    debug_output_dir.join(format!("before_pass_{}_{}", pass_index, pass_info.name)),
                    ssa,
                    format!("before {}: {}", pass_index, pass_info.name),
                );
            }
        }
    }

    fn output_final_debug_info(&mut self, ssa: &mut SSA<V>) {
        if self.cfg.is_none() {
            self.cfg = Some(FlowAnalysis::run(ssa));
        }
        if self.types_valid {
            ssa.typecheck(&self.get_cfg());
        }
        let Some(debug_output_dir) = &self.debug_output_dir else {
            return;
        };
        if let Some(cfg) = &self.cfg {
            cfg.generate_images(debug_output_dir.join("final_result"), ssa, "final result".to_string());
        }
    }

    fn initialize_pass_data(&mut self, ssa: &mut SSA<V>, pass_info: &PassInfo) {
        if (pass_info.needs.contains(&DataPoint::CFG)
            || pass_info.needs.contains(&DataPoint::Types))
            && self.cfg.is_none()
        {
            self.cfg = Some(FlowAnalysis::run(ssa));
        }
        if pass_info.needs.contains(&DataPoint::Types) && !self.types_valid {
            ssa.typecheck(&self.get_cfg());
            self.types_valid = true;
        }
    }

    fn tear_down_pass_data(&mut self, pass_info: &PassInfo) {
        if pass_info.invalidates.contains(&DataPoint::CFG) {
            self.cfg = None;
        }
        if pass_info.invalidates.contains(&DataPoint::Types) {
            self.types_valid = false;
        }
    }
}

impl<V> PassManager<V> {
    pub fn get_cfg(&self) -> &FlowAnalysis {
        match &self.current_pass_info {
            Some(pass_info) => {
                if !pass_info.needs.contains(&DataPoint::CFG) {
                    panic!(
                        "Pass {} does not need CFG but tries to access it",
                        pass_info.name
                    );
                }
            }
            None => {}
        }
        self.cfg.as_ref().unwrap()
    }
}
