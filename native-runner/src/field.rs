//! BN254 Field Element Utilities
//!
//! Handles conversion between decimal strings and Montgomery form.

use ark_bn254::Fr;
use ark_ff::PrimeField;

/// Field element as 4 x u64 limbs in Montgomery form
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct FieldElement {
    pub limbs: [u64; 4],
}

impl FieldElement {
    /// Create a zero field element
    pub fn zero() -> Self {
        Self { limbs: [0; 4] }
    }

    /// Convert to hex string for JSON output
    pub fn to_hex(&self) -> String {
        format!(
            "0x{:016x}{:016x}{:016x}{:016x}",
            self.limbs[3], self.limbs[2], self.limbs[1], self.limbs[0]
        )
    }
}

/// Convert a decimal string to Montgomery form field element
pub fn to_montgomery(value: &str) -> FieldElement {
    // Parse the decimal string
    let fr = if value.starts_with("0x") || value.starts_with("0X") {
        // Hex input
        let hex = &value[2..];
        let bytes = hex::decode(hex).expect("Invalid hex string");
        Fr::from_be_bytes_mod_order(&bytes)
    } else {
        // Decimal input
        let n: num_bigint::BigUint = value.parse().expect("Invalid decimal string");
        let bytes = n.to_bytes_be();
        Fr::from_be_bytes_mod_order(&bytes)
    };

    // Extract Montgomery form limbs
    let limbs = fr.0.0;
    FieldElement { limbs }
}

/// Convert Montgomery form field element back to decimal string
pub fn from_montgomery(fe: &FieldElement) -> String {
    use ark_ff::BigInteger;

    let fr = Fr::new_unchecked(ark_ff::BigInt::new(fe.limbs));
    // Convert to standard form and then to string
    let big_int = fr.into_bigint();

    // Convert limbs to big integer
    let mut result = num_bigint::BigUint::from(0u64);
    for (i, limb) in big_int.0.iter().enumerate() {
        result += num_bigint::BigUint::from(*limb) << (64 * i);
    }

    result.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_roundtrip() {
        let values = ["0", "1", "2", "42", "12345678901234567890"];
        for v in values {
            let fe = to_montgomery(v);
            let back = from_montgomery(&fe);
            assert_eq!(v, back, "Roundtrip failed for {}", v);
        }
    }

    #[test]
    fn test_known_values() {
        // 2 in Montgomery form
        let two = to_montgomery("2");
        assert_eq!(two.limbs[0], 0x592c68389ffffff6);

        // 3 in Montgomery form
        let three = to_montgomery("3");
        assert_eq!(three.limbs[0], 0x05c29c54effffff1);
    }
}
