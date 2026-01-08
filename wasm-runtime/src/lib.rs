//! Runtime Library for Spartan VM WASM
//!
//! Provides BN254 field arithmetic functions called by LLVM-generated WASM code.
//! Field elements are [4 x i64] arrays in Montgomery form, passed by value.

use ark_bn254::Fr;
use ark_ff::BigInt;

#[repr(C)]
#[derive(Clone, Copy)]
pub struct FieldElement {
    pub limbs: [u64; 4],
}

impl FieldElement {
    #[inline]
    fn to_fr(&self) -> Fr {
        Fr::new_unchecked(BigInt::new(self.limbs))
    }

    #[inline]
    fn from_fr(fr: Fr) -> Self {
        Self { limbs: fr.0 .0 }
    }
}

#[no_mangle]
pub extern "C" fn __field_mul(a: FieldElement, b: FieldElement) -> FieldElement {
    FieldElement::from_fr(a.to_fr() * b.to_fr())
}

#[no_mangle]
pub extern "C" fn __field_add(a: FieldElement, b: FieldElement) -> FieldElement {
    FieldElement::from_fr(a.to_fr() + b.to_fr())
}

#[no_mangle]
pub extern "C" fn __field_sub(a: FieldElement, b: FieldElement) -> FieldElement {
    FieldElement::from_fr(a.to_fr() - b.to_fr())
}

#[no_mangle]
pub extern "C" fn __field_div(a: FieldElement, b: FieldElement) -> FieldElement {
    FieldElement::from_fr(a.to_fr() / b.to_fr())
}
