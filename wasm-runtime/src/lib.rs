//! Runtime Library for Spartan VM
//!
//! This library provides BN254 field arithmetic functions that are called
//! by the LLVM-generated code.
//!
//! Field elements are represented as [4 x u64] arrays in Montgomery form.
//!
//! Native Calling Convention (pointer-based for cross-platform ABI compatibility):
//!   void __field_add(ptr result, ptr a, ptr b)
//!
//! WASM Calling Convention (for wasm32 target):
//!   void __field_add(i32 result_ptr, i64 a0..a3, i64 b0..b3)

use ark_bn254::Fr;
use ark_ff::BigInt;

/// Field element as 4 x u64 limbs
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

// =============================================================================
// Native calling convention (pointer-based for cross-platform ABI)
// AAPCS64 passes 32-byte structs by reference, so we use explicit pointers
// to ensure consistent behavior across all platforms.
// =============================================================================

/// Field addition: (a + b) mod p
///
/// # Safety
/// All pointers must be valid and properly aligned for FieldElement.
#[no_mangle]
pub unsafe extern "C" fn __field_add(
    result: *mut FieldElement,
    a: *const FieldElement,
    b: *const FieldElement,
) {
    let sum = (*a).to_fr() + (*b).to_fr();
    *result = FieldElement::from_fr(sum);
}

/// Field subtraction: (a - b) mod p
///
/// # Safety
/// All pointers must be valid and properly aligned for FieldElement.
#[no_mangle]
pub unsafe extern "C" fn __field_sub(
    result: *mut FieldElement,
    a: *const FieldElement,
    b: *const FieldElement,
) {
    let diff = (*a).to_fr() - (*b).to_fr();
    *result = FieldElement::from_fr(diff);
}

/// Field multiplication: (a * b) mod p in Montgomery form
///
/// # Safety
/// All pointers must be valid and properly aligned for FieldElement.
#[no_mangle]
pub unsafe extern "C" fn __field_mul(
    result: *mut FieldElement,
    a: *const FieldElement,
    b: *const FieldElement,
) {
    let prod = (*a).to_fr() * (*b).to_fr();
    *result = FieldElement::from_fr(prod);
}

/// Field division: (a / b) mod p
///
/// # Safety
/// All pointers must be valid and properly aligned for FieldElement.
/// b must not be zero.
#[no_mangle]
pub unsafe extern "C" fn __field_div(
    result: *mut FieldElement,
    a: *const FieldElement,
    b: *const FieldElement,
) {
    let quot = (*a).to_fr() / (*b).to_fr();
    *result = FieldElement::from_fr(quot);
}

// =============================================================================
// WASM calling convention (pointer-based) - for wasm32 target
// =============================================================================

#[cfg(target_arch = "wasm32")]
mod wasm {
    use super::*;

    /// Convert 4 i64 limbs to ark Fr
    #[inline]
    fn limbs_to_fr(l0: i64, l1: i64, l2: i64, l3: i64) -> Fr {
        let limbs = [l0 as u64, l1 as u64, l2 as u64, l3 as u64];
        Fr::new_unchecked(BigInt::new(limbs))
    }

    /// Write Fr to memory at ptr
    #[inline]
    unsafe fn write_fr(ptr: *mut u64, fr: Fr) {
        let limbs = fr.0 .0;
        *ptr = limbs[0];
        *ptr.add(1) = limbs[1];
        *ptr.add(2) = limbs[2];
        *ptr.add(3) = limbs[3];
    }

    #[no_mangle]
    pub extern "C" fn __field_add_wasm(
        result_ptr: i32,
        a0: i64, a1: i64, a2: i64, a3: i64,
        b0: i64, b1: i64, b2: i64, b3: i64,
    ) {
        let a = limbs_to_fr(a0, a1, a2, a3);
        let b = limbs_to_fr(b0, b1, b2, b3);
        unsafe { write_fr(result_ptr as *mut u64, a + b); }
    }

    #[no_mangle]
    pub extern "C" fn __field_sub_wasm(
        result_ptr: i32,
        a0: i64, a1: i64, a2: i64, a3: i64,
        b0: i64, b1: i64, b2: i64, b3: i64,
    ) {
        let a = limbs_to_fr(a0, a1, a2, a3);
        let b = limbs_to_fr(b0, b1, b2, b3);
        unsafe { write_fr(result_ptr as *mut u64, a - b); }
    }

    #[no_mangle]
    pub extern "C" fn __field_mul_wasm(
        result_ptr: i32,
        a0: i64, a1: i64, a2: i64, a3: i64,
        b0: i64, b1: i64, b2: i64, b3: i64,
    ) {
        let a = limbs_to_fr(a0, a1, a2, a3);
        let b = limbs_to_fr(b0, b1, b2, b3);
        unsafe { write_fr(result_ptr as *mut u64, a * b); }
    }

    #[no_mangle]
    pub extern "C" fn __field_div_wasm(
        result_ptr: i32,
        a0: i64, a1: i64, a2: i64, a3: i64,
        b0: i64, b1: i64, b2: i64, b3: i64,
    ) {
        let a = limbs_to_fr(a0, a1, a2, a3);
        let b = limbs_to_fr(b0, b1, b2, b3);
        unsafe { write_fr(result_ptr as *mut u64, a / b); }
    }
}
