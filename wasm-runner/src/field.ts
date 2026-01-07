/**
 * BN254 Field Element Utilities
 *
 * Field elements are represented as 4 x 64-bit limbs in Montgomery form.
 * This matches the representation used by ark-bn254 and the wasm-runtime.
 */

// BN254 scalar field modulus
// p = 21888242871839275222246405745257275088548364400416034343698204186575808495617
export const MODULUS = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;

// R = 2^256 mod p (Montgomery R)
export const R = 6350874878119819312338956282401532410528162663560392320966563075034087161851n;

// R^2 mod p (for toMontgomery conversion)
export const R2 = 944936681149208446651664254269745548490766851729442924617792859073125903783n;

// R^-1 mod p (for fromMontgomery conversion)
export const R_INV = 9915499612839321149637521777990102151350674507940716049588462388200839649614n;

// Mask for 64-bit values
const MASK_64 = (1n << 64n) - 1n;

/**
 * A field element as 4 x u64 limbs in Montgomery form
 */
export type FieldElement = [bigint, bigint, bigint, bigint];

/**
 * Modular multiplication: (a * b) mod p
 */
function mulMod(a: bigint, b: bigint, p: bigint): bigint {
  return ((a % p) * (b % p)) % p;
}

/**
 * Convert a standard field element value to Montgomery form
 * Montgomery form: value * R mod p
 */
export function toMontgomery(value: bigint): FieldElement {
  // Ensure value is in range [0, p)
  let v = value % MODULUS;
  if (v < 0n) v += MODULUS;

  // Multiply by R^2 and reduce to get value * R mod p
  // This uses the identity: (a * R^2) * R^-1 = a * R mod p
  // But we do it directly: value * R mod p
  const montgomery = mulMod(v, R, MODULUS);

  return bigintToLimbs(montgomery);
}

/**
 * Convert from Montgomery form back to standard representation
 * Standard form: montgomeryValue * R^-1 mod p
 */
export function fromMontgomery(limbs: FieldElement): bigint {
  const montgomery = limbsToBigint(limbs);
  return mulMod(montgomery, R_INV, MODULUS);
}

/**
 * Convert a bigint to 4 x 64-bit limbs (little-endian)
 */
export function bigintToLimbs(value: bigint): FieldElement {
  const limb0 = value & MASK_64;
  const limb1 = (value >> 64n) & MASK_64;
  const limb2 = (value >> 128n) & MASK_64;
  const limb3 = (value >> 192n) & MASK_64;
  return [limb0, limb1, limb2, limb3];
}

/**
 * Convert 4 x 64-bit limbs to a bigint (little-endian)
 */
export function limbsToBigint(limbs: FieldElement): bigint {
  return limbs[0] | (limbs[1] << 64n) | (limbs[2] << 128n) | (limbs[3] << 192n);
}

/**
 * Convert a field element (4 limbs) to bytes (32 bytes, little-endian)
 */
export function fieldToBytes(limbs: FieldElement): Uint8Array {
  const bytes = new Uint8Array(32);
  const view = new DataView(bytes.buffer);

  // Write each 64-bit limb in little-endian
  view.setBigUint64(0, limbs[0], true);
  view.setBigUint64(8, limbs[1], true);
  view.setBigUint64(16, limbs[2], true);
  view.setBigUint64(24, limbs[3], true);

  return bytes;
}

/**
 * Convert bytes (32 bytes, little-endian) to a field element (4 limbs)
 */
export function bytesToField(bytes: Uint8Array): FieldElement {
  if (bytes.length !== 32) {
    throw new Error(`Expected 32 bytes, got ${bytes.length}`);
  }

  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);

  return [
    view.getBigUint64(0, true),
    view.getBigUint64(8, true),
    view.getBigUint64(16, true),
    view.getBigUint64(24, true),
  ];
}

/**
 * Convert a field element to a hex string (for JSON output)
 */
export function fieldToHex(limbs: FieldElement): string {
  const value = fromMontgomery(limbs);
  return '0x' + value.toString(16).padStart(64, '0');
}

/**
 * Parse a decimal or hex string to a field element in Montgomery form
 */
export function parseFieldElement(str: string): FieldElement {
  let value: bigint;

  if (str.startsWith('0x') || str.startsWith('0X')) {
    value = BigInt(str);
  } else {
    value = BigInt(str);
  }

  return toMontgomery(value);
}

/**
 * Create a zero field element
 */
export function zero(): FieldElement {
  return [0n, 0n, 0n, 0n];
}

/**
 * Create a one field element (in Montgomery form, this is R mod p)
 */
export function one(): FieldElement {
  return toMontgomery(1n);
}
