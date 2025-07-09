//! SSA generation from Noir SSA structures

pub mod type_converter;
pub mod function_converter;
pub mod converter;

pub use type_converter::TypeConverter;
pub use function_converter::FunctionConverter;
pub use converter::SsaConverter;