use ark_bn254::Fr;
use ark_ff::BigInt;

fn main() {
    // My test values
    let x_limbs: [u64; 4] = [
        6425625360762666998,
        7924344314350639699,
        14762033076929465436,
        2023505479389396574
    ];
    let y_limbs: [u64; 4] = [
        415066004289224689,
        11886516471525959549,
        3696305541684646538,
        3035258219084094862
    ];

    let x = Fr::new_unchecked(BigInt::new(x_limbs));
    let y = Fr::new_unchecked(BigInt::new(y_limbs));

    println!("x (normal): {}", x);
    println!("y (normal): {}", y);

    let sum = x + y;
    println!("x + y (normal): {}", sum);
    println!("x + y (montgomery): {:?}", sum.0.0);

    // Hex format
    let limbs = sum.0.0;
    println!("x + y hex: [0x{:016x}, 0x{:016x}, 0x{:016x}, 0x{:016x}]",
             limbs[0], limbs[1], limbs[2], limbs[3]);
}
