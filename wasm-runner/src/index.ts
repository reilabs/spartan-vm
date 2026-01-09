#!/usr/bin/env node
/**
 * Spartan WASM Runner CLI
 */

import * as fs from 'fs';
import { parseInputs } from './input.js';
import { run, writeResult } from './runner.js';

function printUsage(): void {
  console.log(`
Usage: spartan-wasm-runner <wasm-file> [options]

Options:
  -i, --input <path>   Path to Prover.toml (default: ./Prover.toml)
  -o, --output <path>  Output JSON file (default: ./output.json)
  -h, --help           Show this help
`);
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);

  if (args.length < 1 || args.includes('-h') || args.includes('--help')) {
    printUsage();
    process.exit(args.length < 1 ? 1 : 0);
  }

  const wasmPath = args[0];
  let inputPath = './Prover.toml';
  let outputPath = './output.json';

  for (let i = 1; i < args.length; i++) {
    if (args[i] === '-i' || args[i] === '--input') inputPath = args[++i];
    else if (args[i] === '-o' || args[i] === '--output') outputPath = args[++i];
  }

  // Validate paths
  if (!fs.existsSync(wasmPath)) {
    console.error(`Error: WASM file not found: ${wasmPath}`);
    process.exit(1);
  }
  if (!fs.existsSync(`${wasmPath}.meta.json`)) {
    console.error(`Error: Metadata not found: ${wasmPath}.meta.json`);
    process.exit(1);
  }
  if (!fs.existsSync(inputPath)) {
    console.error(`Error: Input file not found: ${inputPath}`);
    process.exit(1);
  }

  try {
    const { inputs, metadata } = parseInputs(wasmPath, inputPath);
    console.log(`Running ${wasmPath} with ${inputs.length} inputs...`);

    const start = performance.now();
    const result = await run(wasmPath, inputs, metadata);
    const elapsed = performance.now() - start;

    writeResult(result, outputPath);
    console.log(`Done in ${elapsed.toFixed(0)}ms`);
    console.log(`  Witnesses: ${result.witnesses.length}`);
    console.log(`  Constraints: ${result.constraints.a.length}`);
    console.log(`  Output: ${outputPath}`);
  } catch (error) {
    console.error('Error:', error instanceof Error ? error.message : error);
    process.exit(1);
  }
}

main();
