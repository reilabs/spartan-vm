//! WASM Runtime Library for Spartan VM
//!
//! This library provides BN254 field arithmetic functions that are called
//! by the LLVM-generated code when targeting WebAssembly.
//!
//! Field elements are represented as [4 x u64] arrays in Montgomery form.

use ark_bn254::Fr;
use ark_ff::{BigInt, BigInteger256, Field, MontBackend, PrimeField};

/// Field element represented as 4 u64 limbs in Montgomery form
#[repr(C)]
#[derive(Clone, Copy)]
pub struct FieldElement {
    pub limbs: [u64; 4],
}

impl FieldElement {
    /// Create a new field element from limbs
    #[inline]
    pub const fn new(limbs: [u64; 4]) -> Self {
        Self { limbs }
    }

    /// Create a zero field element
    #[inline]
    pub const fn zero() -> Self {
        Self { limbs: [0, 0, 0, 0] }
    }

    /// Create a one field element (in Montgomery form)
    #[inline]
    pub fn one() -> Self {
        Self::from_fr(Fr::from(1u64))
    }

    /// Convert from ark_bn254::Fr
    #[inline]
    pub fn from_fr(fr: Fr) -> Self {
        Self { limbs: fr.0 .0 }
    }

    /// Convert to ark_bn254::Fr
    #[inline]
    pub fn to_fr(self) -> Fr {
        // Directly construct Fr from Montgomery form limbs
        Fr::new_unchecked(BigInt::new(self.limbs))
    }
}

/// Field addition
#[no_mangle]
pub extern "C" fn __field_add(a: FieldElement, b: FieldElement) -> FieldElement {
    let a_fr = a.to_fr();
    let b_fr = b.to_fr();
    let sum = a_fr + b_fr;
    FieldElement::from_fr(sum)
}

/// Field subtraction
#[no_mangle]
pub extern "C" fn __field_sub(a: FieldElement, b: FieldElement) -> FieldElement {
    let a_fr = a.to_fr();
    let b_fr = b.to_fr();
    let diff = a_fr - b_fr;
    FieldElement::from_fr(diff)
}

/// Field multiplication
#[no_mangle]
pub extern "C" fn __field_mul(a: FieldElement, b: FieldElement) -> FieldElement {
    let a_fr = a.to_fr();
    let b_fr = b.to_fr();
    let product = a_fr * b_fr;
    FieldElement::from_fr(product)
}

/// Field division (multiplication by modular inverse)
#[no_mangle]
pub extern "C" fn __field_div(a: FieldElement, b: FieldElement) -> FieldElement {
    let a_fr = a.to_fr();
    let b_fr = b.to_fr();
    let quotient = a_fr / b_fr;
    FieldElement::from_fr(quotient)
}

/// Field negation
#[no_mangle]
pub extern "C" fn __field_neg(a: FieldElement) -> FieldElement {
    let a_fr = a.to_fr();
    let neg = -a_fr;
    FieldElement::from_fr(neg)
}

/// Field equality check
#[no_mangle]
pub extern "C" fn __field_eq(a: FieldElement, b: FieldElement) -> u32 {
    let a_fr = a.to_fr();
    let b_fr = b.to_fr();
    if a_fr == b_fr {
        1
    } else {
        0
    }
}

/// Field element from u64
#[no_mangle]
pub extern "C" fn __field_from_u64(value: u64) -> FieldElement {
    let fr = Fr::from(value);
    FieldElement::from_fr(fr)
}

/// Get low 64 bits of field element (converts from Montgomery form first)
#[no_mangle]
pub extern "C" fn __field_to_u64(a: FieldElement) -> u64 {
    let fr = a.to_fr();
    let bigint = fr.into_bigint();
    bigint.0[0]
}

/// Field element square
#[no_mangle]
pub extern "C" fn __field_square(a: FieldElement) -> FieldElement {
    let a_fr = a.to_fr();
    let squared = a_fr.square();
    FieldElement::from_fr(squared)
}

/// Field element power
#[no_mangle]
pub extern "C" fn __field_pow(a: FieldElement, exp: u64) -> FieldElement {
    let a_fr = a.to_fr();
    let powered = a_fr.pow([exp]);
    FieldElement::from_fr(powered)
}

/// Field element inverse
#[no_mangle]
pub extern "C" fn __field_inverse(a: FieldElement) -> FieldElement {
    let a_fr = a.to_fr();
    let inv = a_fr.inverse().expect("Cannot invert zero");
    FieldElement::from_fr(inv)
}

/// Assert two field elements are equal (for R1CS constraints)
#[no_mangle]
pub extern "C" fn __field_assert_eq(a: FieldElement, b: FieldElement) {
    let a_fr = a.to_fr();
    let b_fr = b.to_fr();
    assert!(
        a_fr == b_fr,
        "Field assertion failed: values are not equal"
    );
}

/// Check R1CS constraint: a * b == c
#[no_mangle]
pub extern "C" fn __r1cs_constrain(a: FieldElement, b: FieldElement, c: FieldElement) {
    let a_fr = a.to_fr();
    let b_fr = b.to_fr();
    let c_fr = c.to_fr();
    let product = a_fr * b_fr;
    assert!(product == c_fr, "R1CS constraint failed: a * b != c");
}
