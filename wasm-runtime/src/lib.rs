//! WASM Runtime Library for Spartan VM
//!
//! This library provides BN254 field arithmetic functions that are called
//! by the LLVM-generated code when targeting WebAssembly.
//!
//! Field elements are represented as [4 x i64] (internally u64) in Montgomery form.
//!
//! WASM Calling Convention:
//! - result_ptr: i32 - pointer where to write the 32-byte result
//! - a0, a1, a2, a3: i64 - 4 limbs of first operand
//! - b0, b1, b2, b3: i64 - 4 limbs of second operand (for binary ops)

use ark_bn254::Fr;
use ark_ff::BigInt;

/// Convert 4 i64 limbs to ark Fr
#[inline]
fn limbs_to_fr(l0: i64, l1: i64, l2: i64, l3: i64) -> Fr {
    // WASM i64 are signed, reinterpret as unsigned
    let limbs = [l0 as u64, l1 as u64, l2 as u64, l3 as u64];
    Fr::new_unchecked(BigInt::new(limbs))
}

/// Write Fr to memory at ptr as 4 x u64 limbs (little-endian)
#[inline]
unsafe fn write_fr(ptr: *mut u64, fr: Fr) {
    let limbs = fr.0 .0;
    *ptr = limbs[0];
    *ptr.add(1) = limbs[1];
    *ptr.add(2) = limbs[2];
    *ptr.add(3) = limbs[3];
}

/// Field addition: (a + b) mod p
#[no_mangle]
pub extern "C" fn __field_add(
    result_ptr: i32,
    a0: i64,
    a1: i64,
    a2: i64,
    a3: i64,
    b0: i64,
    b1: i64,
    b2: i64,
    b3: i64,
) {
    let a = limbs_to_fr(a0, a1, a2, a3);
    let b = limbs_to_fr(b0, b1, b2, b3);
    let result = a + b;
    unsafe {
        write_fr(result_ptr as *mut u64, result);
    }
}

/// Field subtraction: (a - b) mod p
#[no_mangle]
pub extern "C" fn __field_sub(
    result_ptr: i32,
    a0: i64,
    a1: i64,
    a2: i64,
    a3: i64,
    b0: i64,
    b1: i64,
    b2: i64,
    b3: i64,
) {
    let a = limbs_to_fr(a0, a1, a2, a3);
    let b = limbs_to_fr(b0, b1, b2, b3);
    let result = a - b;
    unsafe {
        write_fr(result_ptr as *mut u64, result);
    }
}

/// Field multiplication: (a * b) mod p in Montgomery form
#[no_mangle]
pub extern "C" fn __field_mul(
    result_ptr: i32,
    a0: i64,
    a1: i64,
    a2: i64,
    a3: i64,
    b0: i64,
    b1: i64,
    b2: i64,
    b3: i64,
) {
    let a = limbs_to_fr(a0, a1, a2, a3);
    let b = limbs_to_fr(b0, b1, b2, b3);
    let result = a * b;
    unsafe {
        write_fr(result_ptr as *mut u64, result);
    }
}

/// Field division: (a / b) mod p
#[no_mangle]
pub extern "C" fn __field_div(
    result_ptr: i32,
    a0: i64,
    a1: i64,
    a2: i64,
    a3: i64,
    b0: i64,
    b1: i64,
    b2: i64,
    b3: i64,
) {
    let a = limbs_to_fr(a0, a1, a2, a3);
    let b = limbs_to_fr(b0, b1, b2, b3);
    let result = a / b;
    unsafe {
        write_fr(result_ptr as *mut u64, result);
    }
}
