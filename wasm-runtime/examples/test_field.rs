use ark_bn254::Fr;
use ark_ff::{BigInteger, Field, PrimeField, BigInt};

fn main() {
    // Values from the C test
    let one_limbs: [u64; 4] = [0xac96341c4ffffffeu64, 0x36fc76959f60cd29, 0x666ea36f7879462e, 0x0e0a77c19a07df2f];
    let two_limbs: [u64; 4] = [0xac96341c4ffffffbu64, 0x36fc76959f60cd29, 0x666ea36f7879462e, 0x0e0a77c19a07df2f];
    let three_limbs: [u64; 4] = [0xac96341c4ffffff8u64, 0x36fc76959f60cd29, 0x666ea36f7879462e, 0x0e0a77c19a07df2f];

    // Create Fr from montgomery form
    let one = Fr::new_unchecked(BigInt::new(one_limbs));
    let two = Fr::new_unchecked(BigInt::new(two_limbs));
    let three = Fr::new_unchecked(BigInt::new(three_limbs));

    println!("one (normal form): {}", one);
    println!("two (normal form): {}", two);
    println!("three (normal form): {}", three);

    // Test multiplication
    let two_sq = two * two;
    let two_times_three = two * three;
    let three_times_two = three * two;

    println!("\n2 * 2 = {} (montgomery: {:?})", two_sq, two_sq.0.0);
    println!("2 * 3 = {} (montgomery: {:?})", two_times_three, two_times_three.0.0);
    println!("3 * 2 = {} (montgomery: {:?})", three_times_two, three_times_two.0.0);

    // Test addition
    let two_plus_three = two + three;
    println!("\n2 + 3 = {} (montgomery: {:?})", two_plus_three, two_plus_three.0.0);

    // Create fresh values from scratch
    println!("\n--- Creating from scratch ---");
    let fresh_one = Fr::from(1u64);
    let fresh_two = Fr::from(2u64);
    let fresh_three = Fr::from(3u64);
    println!("1 in montgomery: {:?}", fresh_one.0.0);
    println!("2 in montgomery: {:?}", fresh_two.0.0);
    println!("3 in montgomery: {:?}", fresh_three.0.0);
    println!("4 in montgomery: {:?}", Fr::from(4u64).0.0);
    println!("6 in montgomery: {:?}", Fr::from(6u64).0.0);
}
