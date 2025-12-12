//! SSA generation from Noir SSA structures

pub mod converter;
pub mod function_converter;
pub mod type_converter;

pub use converter::SsaConverter;
pub use function_converter::FunctionConverter;
pub use type_converter::TypeConverter;
