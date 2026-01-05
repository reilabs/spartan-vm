//! Spartan VM Interpreter
//!
//! This crate contains the core VM execution engine for Spartan, including:
//! - Bytecode definitions and dispatch mechanisms
//! - VM interpreter implementation
//! - Array handling for dynamic data
//! - Memory layout types for witness and constraint data

pub mod array;
pub mod bytecode;
pub mod interpreter;
pub mod layouts;

// Re-export commonly used types
pub use layouts::{ConstraintsLayout, WitnessLayout};

// Re-export Field type for convenience
pub use ark_bn254::Fr as Field;
