/**
 * WASM Runner - executes generated WASM with JavaScript runtime functions
 */

import * as fs from 'fs';
import { FieldElement, fieldToHex } from './field.js';
import { ProgramMetadata } from './input.js';

const FIELD_SIZE = 32; // 4 x i64 = 32 bytes

export interface RunResult {
  witnesses: string[];
  constraints: {
    a: string[];
    b: string[];
    c: string[];
  };
}

const MODULUS = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
const R_INV = 9915499612839321149637521777990102151350674507940716049588462388200839649614n;
const MASK64 = (1n << 64n) - 1n;

// Convert signed i64 to unsigned u64
function toU64(v: bigint): bigint {
  return v < 0n ? v + (1n << 64n) : v;
}

// Convert 4 signed i64 limbs to a single bigint
function limbsToValue(l0: bigint, l1: bigint, l2: bigint, l3: bigint): bigint {
  return toU64(l0) | (toU64(l1) << 64n) | (toU64(l2) << 128n) | (toU64(l3) << 192n);
}

// Convert bigint to 4 unsigned limbs
function valueToLimbs(v: bigint): FieldElement {
  return [v & MASK64, (v >> 64n) & MASK64, (v >> 128n) & MASK64, (v >> 192n) & MASK64];
}

/**
 * BN254 field multiplication in Montgomery form
 */
function fieldMul(a0: bigint, a1: bigint, a2: bigint, a3: bigint,
                  b0: bigint, b1: bigint, b2: bigint, b3: bigint): FieldElement {
  const aVal = limbsToValue(a0, a1, a2, a3);
  const bVal = limbsToValue(b0, b1, b2, b3);
  const product = (aVal * bVal * R_INV) % MODULUS;
  return valueToLimbs(product);
}

/**
 * Read a field element from memory
 */
function readField(view: DataView, ptr: number): FieldElement {
  return [
    view.getBigUint64(ptr, true),
    view.getBigUint64(ptr + 8, true),
    view.getBigUint64(ptr + 16, true),
    view.getBigUint64(ptr + 24, true),
  ];
}

/**
 * Write a field element to memory
 */
function writeField(view: DataView, ptr: number, field: FieldElement): void {
  view.setBigUint64(ptr, field[0], true);
  view.setBigUint64(ptr + 8, field[1], true);
  view.setBigUint64(ptr + 16, field[2], true);
  view.setBigUint64(ptr + 24, field[3], true);
}

export async function run(
  wasmPath: string,
  inputs: FieldElement[],
  metadata: ProgramMetadata
): Promise<RunResult> {
  // Calculate memory size needed
  const witnessBytes = metadata.witnessCount * FIELD_SIZE;
  const constraintBytes = metadata.constraintCount * FIELD_SIZE;
  const totalBytes = 64 + witnessBytes + constraintBytes * 3; // VM struct + buffers
  const pages = Math.ceil(totalBytes / 65536) + 1;

  // Create memory
  const memory = new WebAssembly.Memory({ initial: pages, maximum: pages * 2 });
  const view = new DataView(memory.buffer);

  // Layout: VM struct at 0, then buffers
  const vmPtr = 0;
  const witnessPtr = 64;
  const aPtr = witnessPtr + witnessBytes;
  const bPtr = aPtr + constraintBytes;
  const cPtr = bPtr + constraintBytes;

  // Initialize VM struct with buffer pointers (these get advanced by write functions)
  view.setUint32(vmPtr, witnessPtr, true);
  view.setUint32(vmPtr + 4, aPtr, true);
  view.setUint32(vmPtr + 8, bPtr, true);
  view.setUint32(vmPtr + 12, cPtr, true);

  // Runtime functions that operate on the shared memory
  const imports: WebAssembly.Imports = {
    env: {
      memory,
      __field_mul: (
        resultPtr: number,
        a0: bigint, a1: bigint, a2: bigint, a3: bigint,
        b0: bigint, b1: bigint, b2: bigint, b3: bigint
      ) => {
        const result = fieldMul(a0, a1, a2, a3, b0, b1, b2, b3);
        const v = new DataView(memory.buffer);
        writeField(v, resultPtr, result);
      },
      __write_witness: (vmPtr: number, v0: bigint, v1: bigint, v2: bigint, v3: bigint) => {
        const v = new DataView(memory.buffer);
        const ptr = v.getUint32(vmPtr, true);
        writeField(v, ptr, [toU64(v0), toU64(v1), toU64(v2), toU64(v3)]);
        v.setUint32(vmPtr, ptr + FIELD_SIZE, true);
      },
      __write_a: (vmPtr: number, v0: bigint, v1: bigint, v2: bigint, v3: bigint) => {
        const v = new DataView(memory.buffer);
        const ptr = v.getUint32(vmPtr + 4, true);
        writeField(v, ptr, [toU64(v0), toU64(v1), toU64(v2), toU64(v3)]);
        v.setUint32(vmPtr + 4, ptr + FIELD_SIZE, true);
      },
      __write_b: (vmPtr: number, v0: bigint, v1: bigint, v2: bigint, v3: bigint) => {
        const v = new DataView(memory.buffer);
        const ptr = v.getUint32(vmPtr + 8, true);
        writeField(v, ptr, [toU64(v0), toU64(v1), toU64(v2), toU64(v3)]);
        v.setUint32(vmPtr + 8, ptr + FIELD_SIZE, true);
      },
      __write_c: (vmPtr: number, v0: bigint, v1: bigint, v2: bigint, v3: bigint) => {
        const v = new DataView(memory.buffer);
        const ptr = v.getUint32(vmPtr + 12, true);
        writeField(v, ptr, [toU64(v0), toU64(v1), toU64(v2), toU64(v3)]);
        v.setUint32(vmPtr + 12, ptr + FIELD_SIZE, true);
      },
    },
  };

  // Load and run the generated WASM
  const wasmBytes = fs.readFileSync(wasmPath);
  const module = await WebAssembly.compile(wasmBytes);
  const instance = await WebAssembly.instantiate(module, imports);
  const exports = instance.exports as { spartan_main: (...args: (number | bigint)[]) => void };

  // Prepare arguments: vmPtr, then flattened input limbs
  const args: (number | bigint)[] = [vmPtr];
  for (const input of inputs) {
    args.push(input[0], input[1], input[2], input[3]);
  }

  // Execute
  exports.spartan_main(...args);

  // Read output buffers
  const witnesses: FieldElement[] = [];
  const constraintsA: FieldElement[] = [];
  const constraintsB: FieldElement[] = [];
  const constraintsC: FieldElement[] = [];

  for (let i = 0; i < metadata.witnessCount; i++) {
    witnesses.push(readField(view, witnessPtr + i * FIELD_SIZE));
  }
  for (let i = 0; i < metadata.constraintCount; i++) {
    constraintsA.push(readField(view, aPtr + i * FIELD_SIZE));
    constraintsB.push(readField(view, bPtr + i * FIELD_SIZE));
    constraintsC.push(readField(view, cPtr + i * FIELD_SIZE));
  }

  return {
    witnesses: witnesses.map(fieldToHex),
    constraints: {
      a: constraintsA.map(fieldToHex),
      b: constraintsB.map(fieldToHex),
      c: constraintsC.map(fieldToHex),
    },
  };
}

export function writeResult(result: RunResult, outputPath: string): void {
  fs.writeFileSync(outputPath, JSON.stringify(result, null, 2));
}
