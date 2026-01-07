#!/usr/bin/env node
/**
 * Spartan WASM Runner CLI
 *
 * Usage:
 *   spartan-wasm-runner <wasm-file> [options]
 *
 * Options:
 *   --input, -i <path>     Path to Prover.toml (default: ./Prover.toml)
 *   --output, -o <path>    Output JSON file (default: ./output.json)
 *   --runtime, -r <path>   Path to wasm-runtime.wasm
 */

import * as fs from 'fs';
import * as path from 'path';
import { parseInputs } from './input.js';
import { run, writeResult } from './runner.js';

interface CLIOptions {
  wasmPath: string;
  inputPath: string;
  outputPath: string;
}

function printUsage(): void {
  console.log(`
Spartan WASM Runner

Usage:
  spartan-wasm-runner <wasm-file> [options]

Options:
  --input, -i <path>     Path to Prover.toml (default: ./Prover.toml)
  --output, -o <path>    Output JSON file (default: ./output.json)

Examples:
  spartan-wasm-runner output.wasm
  spartan-wasm-runner output.wasm -i Prover.toml -o result.json
`);
}

function parseArgs(args: string[]): CLIOptions | null {
  if (args.length < 1) {
    return null;
  }

  const wasmPath = args[0];
  let inputPath = './Prover.toml';
  let outputPath = './output.json';

  for (let i = 1; i < args.length; i++) {
    const arg = args[i];

    if (arg === '--input' || arg === '-i') {
      inputPath = args[++i];
    } else if (arg === '--output' || arg === '-o') {
      outputPath = args[++i];
    } else if (arg === '--help' || arg === '-h') {
      return null;
    }
  }

  return {
    wasmPath,
    inputPath,
    outputPath,
  };
}

function validatePaths(options: CLIOptions): boolean {
  if (!fs.existsSync(options.wasmPath)) {
    console.error(`Error: WASM file not found: ${options.wasmPath}`);
    return false;
  }

  const metadataPath = `${options.wasmPath}.meta.json`;
  if (!fs.existsSync(metadataPath)) {
    console.error(`Error: Metadata file not found: ${metadataPath}`);
    console.error('The WASM file must have an accompanying .meta.json file');
    return false;
  }

  if (!fs.existsSync(options.inputPath)) {
    console.error(`Error: Input file not found: ${options.inputPath}`);
    return false;
  }

  return true;
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);

  const options = parseArgs(args);
  if (!options) {
    printUsage();
    process.exit(1);
  }

  if (!validatePaths(options)) {
    process.exit(1);
  }

  try {
    console.log(`Loading inputs from ${options.inputPath}...`);
    const { inputs, metadata } = parseInputs(options.wasmPath, options.inputPath);
    console.log(`  Parameters: ${metadata.parameters.map((p) => p.name).join(', ')}`);
    console.log(`  Total inputs: ${inputs.length} field elements`);
    console.log(`  Witnesses: ${metadata.witnessCount}`);
    console.log(`  Constraints: ${metadata.constraintCount}`);

    console.log(`\nRunning WASM...`);
    const { result, timing } = await run(
      options.wasmPath,
      '', // Not used - WASM runtime found automatically
      inputs,
      metadata
    );

    console.log(`\nWriting output to ${options.outputPath}...`);
    writeResult(result, options.outputPath);

    console.log('\nDone!');
    console.log(`  Witnesses written: ${result.witnesses.length}`);
    console.log(`  Constraints written: ${result.constraints.a.length}`);
    console.log(`\nTiming:`);
    console.log(`  Load runtime:    ${timing.loadRuntimeMs.toFixed(2)} ms`);
    console.log(`  Load generated:  ${timing.loadGeneratedMs.toFixed(2)} ms`);
    console.log(`  Execution:       ${timing.executionMs.toFixed(2)} ms`);
    console.log(`  Read output:     ${timing.readOutputMs.toFixed(2)} ms`);
    console.log(`  Total:           ${timing.totalMs.toFixed(2)} ms`);
  } catch (error) {
    console.error('Error:', error instanceof Error ? error.message : error);
    process.exit(1);
  }
}

main();
