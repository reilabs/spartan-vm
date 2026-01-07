/**
 * WASM Runner
 *
 * Loads and executes the generated WASM with WASM-based field operations.
 */

import * as fs from 'fs';
import * as path from 'path';
import { fileURLToPath } from 'url';
import {
  MemoryLayout,
  calculateLayout,
  createMemory,
  initializeVMStruct,
  initializeBuffers,
  readOutputBuffers,
  VMOutput,
} from './memory.js';
import { FieldElement, fieldToHex, MODULUS } from './field.js';
import { ProgramMetadata } from './input.js';

/**
 * Result of running the WASM program
 */
export interface RunResult {
  witnesses: string[];
  constraints: {
    a: string[];
    b: string[];
    c: string[];
  };
}

/**
 * The generated WASM module exports
 */
interface GeneratedWasmExports {
  spartan_main: (...args: (number | bigint)[]) => void;
}

/**
 * The WASM runtime module exports
 */
interface RuntimeWasmExports {
  __field_add: (
    resultPtr: number,
    a0: bigint,
    a1: bigint,
    a2: bigint,
    a3: bigint,
    b0: bigint,
    b1: bigint,
    b2: bigint,
    b3: bigint
  ) => void;
  __field_sub: (
    resultPtr: number,
    a0: bigint,
    a1: bigint,
    a2: bigint,
    a3: bigint,
    b0: bigint,
    b1: bigint,
    b2: bigint,
    b3: bigint
  ) => void;
  __field_mul: (
    resultPtr: number,
    a0: bigint,
    a1: bigint,
    a2: bigint,
    a3: bigint,
    b0: bigint,
    b1: bigint,
    b2: bigint,
    b3: bigint
  ) => void;
  __field_div: (
    resultPtr: number,
    a0: bigint,
    a1: bigint,
    a2: bigint,
    a3: bigint,
    b0: bigint,
    b1: bigint,
    b2: bigint,
    b3: bigint
  ) => void;
}

/**
 * Convert VMOutput to RunResult with hex strings
 */
function outputToResult(output: VMOutput): RunResult {
  return {
    witnesses: output.witnesses.map(fieldToHex),
    constraints: {
      a: output.constraintsA.map(fieldToHex),
      b: output.constraintsB.map(fieldToHex),
      c: output.constraintsC.map(fieldToHex),
    },
  };
}

/**
 * Find the wasm-runtime WASM file
 */
function findRuntimeWasm(): string {
  // Get directory of this module (ES modules compatible)
  const __filename = fileURLToPath(import.meta.url);
  const __dirname = path.dirname(__filename);

  // Try different possible locations
  const candidates = [
    // Relative to this package (when installed)
    path.join(__dirname, '..', '..', 'wasm-runtime.wasm'),
    // Relative to workspace root (during development)
    path.join(
      __dirname,
      '..',
      '..',
      '..',
      'target',
      'wasm32-unknown-unknown',
      'release',
      'spartan_wasm_runtime.wasm'
    ),
    // In the current directory
    'wasm-runtime.wasm',
    // In the workspace target directory
    '/home/developer/workspace/target/wasm32-unknown-unknown/release/spartan_wasm_runtime.wasm',
  ];

  for (const candidate of candidates) {
    if (fs.existsSync(candidate)) {
      return candidate;
    }
  }

  throw new Error(
    'Could not find wasm-runtime.wasm. Tried:\n' + candidates.join('\n')
  );
}

/**
 * Load and instantiate the WASM runtime with shared memory
 */
async function loadRuntime(
  memory: WebAssembly.Memory
): Promise<RuntimeWasmExports> {
  const runtimePath = findRuntimeWasm();
  const wasmBytes = fs.readFileSync(runtimePath);
  const module = await WebAssembly.compile(wasmBytes);

  const imports: WebAssembly.Imports = {
    env: {
      memory,
    },
  };

  const instance = await WebAssembly.instantiate(module, imports);
  return instance.exports as unknown as RuntimeWasmExports;
}

/**
 * Build import object for the generated WASM using WASM runtime
 */
function buildImports(
  memory: WebAssembly.Memory,
  runtime: RuntimeWasmExports
): WebAssembly.Imports {
  return {
    env: {
      memory,
      __field_add: runtime.__field_add,
      __field_sub: runtime.__field_sub,
      __field_mul: runtime.__field_mul,
      __field_div: runtime.__field_div,
    },
  };
}

/**
 * Load and instantiate the generated WASM module
 */
async function loadGenerated(
  wasmPath: string,
  imports: WebAssembly.Imports
): Promise<GeneratedWasmExports> {
  const wasmBytes = fs.readFileSync(wasmPath);
  const module = await WebAssembly.compile(wasmBytes);
  const instance = await WebAssembly.instantiate(module, imports);

  return instance.exports as unknown as GeneratedWasmExports;
}

/**
 * Prepare main() arguments from VM pointer and input field elements
 *
 * Arguments: [vm_ptr, input0_limb0, input0_limb1, input0_limb2, input0_limb3, input1_limb0, ...]
 */
function prepareMainArgs(
  vmPtr: number,
  inputs: FieldElement[]
): (number | bigint)[] {
  const args: (number | bigint)[] = [vmPtr];

  for (const input of inputs) {
    // Add all 4 limbs of the field element
    args.push(input[0], input[1], input[2], input[3]);
  }

  return args;
}

/**
 * Timing information from WASM execution
 */
export interface TimingInfo {
  loadRuntimeMs: number;
  loadGeneratedMs: number;
  executionMs: number;
  readOutputMs: number;
  totalMs: number;
}

/**
 * Run the WASM program
 */
export async function run(
  wasmPath: string,
  _runtimePath: string, // Not used - we find runtime automatically
  inputs: FieldElement[],
  metadata: ProgramMetadata
): Promise<{ result: RunResult; timing: TimingInfo }> {
  const totalStart = performance.now();

  // Calculate memory layout
  const layout = calculateLayout(metadata.witnessCount, metadata.constraintCount);

  // Create shared memory
  const memory = createMemory(layout);

  // Initialize VM struct and zero output buffers
  initializeVMStruct(memory, layout);
  initializeBuffers(memory, layout);

  // Load WASM runtime with shared memory
  const loadRuntimeStart = performance.now();
  const runtime = await loadRuntime(memory);
  const loadRuntimeMs = performance.now() - loadRuntimeStart;

  // Build import object with WASM field operations
  const imports = buildImports(memory, runtime);

  // Load generated WASM
  const loadGeneratedStart = performance.now();
  const generated = await loadGenerated(wasmPath, imports);
  const loadGeneratedMs = performance.now() - loadGeneratedStart;

  // Prepare main() arguments
  const args = prepareMainArgs(layout.vmPtr, inputs);

  // Execute spartan_main()
  const executionStart = performance.now();
  generated.spartan_main(...args);
  const executionMs = performance.now() - executionStart;

  // Read output buffers
  const readOutputStart = performance.now();
  const output = readOutputBuffers(memory, layout);
  const readOutputMs = performance.now() - readOutputStart;

  const totalMs = performance.now() - totalStart;

  const timing: TimingInfo = {
    loadRuntimeMs,
    loadGeneratedMs,
    executionMs,
    readOutputMs,
    totalMs,
  };

  // Convert to result format
  return { result: outputToResult(output), timing };
}

/**
 * Write result to JSON file
 */
export function writeResult(result: RunResult, outputPath: string): void {
  const json = JSON.stringify(result, null, 2);
  fs.writeFileSync(outputPath, json);
}
