/**
 * WASM Memory Management
 *
 * Handles allocation and management of WASM linear memory for the VM.
 *
 * Memory Layout:
 * - VM struct: 4 x i32 pointers (16 bytes)
 * - Witness buffer: witnessCount x 32 bytes
 * - Constraint A buffer: constraintCount x 32 bytes
 * - Constraint B buffer: constraintCount x 32 bytes
 * - Constraint C buffer: constraintCount x 32 bytes
 */

import { FieldElement, bytesToField } from './field.js';

// Size of a field element in bytes (4 x 64-bit limbs)
const FIELD_ELEMENT_SIZE = 32;

// Size of a pointer in WASM32 (4 bytes)
const POINTER_SIZE = 4;

// VM struct has 4 pointers
const VM_STRUCT_SIZE = POINTER_SIZE * 4;

// Alignment for field elements (8 bytes for i64 access)
const ALIGNMENT = 8;

/**
 * Memory layout information
 */
export interface MemoryLayout {
  vmPtr: number;
  witnessPtr: number;
  constraintAPtr: number;
  constraintBPtr: number;
  constraintCPtr: number;
  witnessCount: number;
  constraintCount: number;
  totalPages: number;
}

/**
 * Align an offset to the specified alignment
 */
function align(offset: number, alignment: number): number {
  return Math.ceil(offset / alignment) * alignment;
}

/**
 * Calculate total memory needed and buffer offsets
 */
export function calculateLayout(witnessCount: number, constraintCount: number): MemoryLayout {
  // Start at offset 0 for VM struct
  const vmPtr = 0;

  // Witnesses start after VM struct (aligned)
  const witnessPtr = align(VM_STRUCT_SIZE, ALIGNMENT);

  // Constraint A starts after witnesses
  const constraintAPtr = align(witnessPtr + witnessCount * FIELD_ELEMENT_SIZE, ALIGNMENT);

  // Constraint B starts after A
  const constraintBPtr = align(constraintAPtr + constraintCount * FIELD_ELEMENT_SIZE, ALIGNMENT);

  // Constraint C starts after B
  const constraintCPtr = align(constraintBPtr + constraintCount * FIELD_ELEMENT_SIZE, ALIGNMENT);

  // Total size needed
  const totalSize = constraintCPtr + constraintCount * FIELD_ELEMENT_SIZE;

  // WASM pages are 64KB each
  const PAGE_SIZE = 65536;
  const totalPages = Math.ceil(totalSize / PAGE_SIZE);

  return {
    vmPtr,
    witnessPtr,
    constraintAPtr,
    constraintBPtr,
    constraintCPtr,
    witnessCount,
    constraintCount,
    totalPages,
  };
}

/**
 * Create WASM memory with sufficient space for all buffers
 */
export function createMemory(layout: MemoryLayout): WebAssembly.Memory {
  return new WebAssembly.Memory({
    initial: layout.totalPages,
    maximum: layout.totalPages * 2, // Allow some growth
  });
}

/**
 * Initialize the VM struct with buffer pointers
 */
export function initializeVMStruct(memory: WebAssembly.Memory, layout: MemoryLayout): void {
  const view = new DataView(memory.buffer);

  // Write 4 pointers to VM struct (little-endian i32)
  view.setUint32(layout.vmPtr + 0, layout.witnessPtr, true);
  view.setUint32(layout.vmPtr + 4, layout.constraintAPtr, true);
  view.setUint32(layout.vmPtr + 8, layout.constraintBPtr, true);
  view.setUint32(layout.vmPtr + 12, layout.constraintCPtr, true);
}

/**
 * Read a field element from memory at the given byte offset
 */
export function readFieldElement(memory: WebAssembly.Memory, offset: number): FieldElement {
  const bytes = new Uint8Array(memory.buffer, offset, FIELD_ELEMENT_SIZE);
  return bytesToField(bytes);
}

/**
 * Read all field elements from a buffer
 */
export function readFieldElements(
  memory: WebAssembly.Memory,
  startOffset: number,
  count: number
): FieldElement[] {
  const elements: FieldElement[] = [];
  for (let i = 0; i < count; i++) {
    const offset = startOffset + i * FIELD_ELEMENT_SIZE;
    elements.push(readFieldElement(memory, offset));
  }
  return elements;
}

/**
 * Output buffers from VM execution
 */
export interface VMOutput {
  witnesses: FieldElement[];
  constraintsA: FieldElement[];
  constraintsB: FieldElement[];
  constraintsC: FieldElement[];
}

/**
 * Read all output buffers from memory after execution
 */
export function readOutputBuffers(memory: WebAssembly.Memory, layout: MemoryLayout): VMOutput {
  return {
    witnesses: readFieldElements(memory, layout.witnessPtr, layout.witnessCount),
    constraintsA: readFieldElements(memory, layout.constraintAPtr, layout.constraintCount),
    constraintsB: readFieldElements(memory, layout.constraintBPtr, layout.constraintCount),
    constraintsC: readFieldElements(memory, layout.constraintCPtr, layout.constraintCount),
  };
}

/**
 * Write a field element to memory at the given byte offset
 */
export function writeFieldElement(
  memory: WebAssembly.Memory,
  offset: number,
  element: FieldElement
): void {
  const view = new DataView(memory.buffer, offset, FIELD_ELEMENT_SIZE);

  // Write 4 x 64-bit limbs in little-endian
  view.setBigUint64(0, element[0], true);
  view.setBigUint64(8, element[1], true);
  view.setBigUint64(16, element[2], true);
  view.setBigUint64(24, element[3], true);
}

/**
 * Zero out a memory region (useful for initializing buffers)
 */
export function zeroMemory(memory: WebAssembly.Memory, offset: number, size: number): void {
  const bytes = new Uint8Array(memory.buffer, offset, size);
  bytes.fill(0);
}

/**
 * Initialize all output buffers to zero
 */
export function initializeBuffers(memory: WebAssembly.Memory, layout: MemoryLayout): void {
  // Zero witness buffer
  zeroMemory(memory, layout.witnessPtr, layout.witnessCount * FIELD_ELEMENT_SIZE);

  // Zero constraint buffers
  zeroMemory(memory, layout.constraintAPtr, layout.constraintCount * FIELD_ELEMENT_SIZE);
  zeroMemory(memory, layout.constraintBPtr, layout.constraintCount * FIELD_ELEMENT_SIZE);
  zeroMemory(memory, layout.constraintCPtr, layout.constraintCount * FIELD_ELEMENT_SIZE);
}
