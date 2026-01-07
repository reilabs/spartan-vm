# Architecture

This document describes the architecture of the Spartan VM project - a Noir-to-R1CS compiler and witness generation engine for the [Spartan proof system](https://eprint.iacr.org/2019/550).

## Project Purpose

This project compiles [Noir](https://noir-lang.org/) programs into everything the Spartan proof system needs:

1. **R1CS constraint matrices** (A, B, C) where constraints have the form `Aw ∘ Bw = Cw`
2. **Witness generation program** (witgen) - computes the witness vector `w` and evaluates `Aw`, `Bw`, `Cw`
3. **Automatic differentiation program** (AD) - computes random linear combinations of R1CS rows needed by Spartan's sumcheck protocol

The key insight for AD: if you view the constraint evaluation as computing `coeffs · A · w` (where `coeffs` are random verifier challenges), then the derivative with respect to `w` is exactly `coeffs · A` - the random linear combination of rows that Spartan needs.

## Compilation Pipeline Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    Noir Source (.nr)                        │
└─────────────────────────┬───────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────────┐
│              Noir Compiler (external)                       │
│         Produces Noir SSA representation                    │
└─────────────────────────┬───────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────────┐
│              SSA Conversion (ssa_gen/)                      │
│         Noir SSA  →  Spartan VM SSA<Empty>                  │
└─────────────────────────┬───────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────────┐
│              Monomorphization Pipeline                      │
│  ┌─────────────────────────────────────────────────────┐    │
│  │ 1. Taint Analysis: classify Pure vs Witness values  │    │
│  │ 2. Monomorphization: specialize generic functions   │    │
│  │ 3. Untaint Control Flow: ensure branches are Pure   │    │
│  └─────────────────────────────────────────────────────┘    │
└─────────────────────────┬───────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────────┐
│              Optimization Passes                            │
│    Mem2Reg, CSE, DCE, Condition Propagation, etc.          │
│    + Explicit Witness pass (taint-aware lowering)          │
└─────────────────────────┬───────────────────────────────────┘
                          │
                          ▼
┌─────────────────────────────────────────────────────────────┐
│              R1CS Generation (r1cs_gen.rs)                  │
│         SSA instructions → R1CS constraints                 │
└──────────┬──────────────────────────────────┬───────────────┘
           │                                  │
           ▼                                  ▼
┌─────────────────────────┐        ┌─────────────────────────┐
│   Witgen Compilation    │        │    AD Compilation       │
│  ┌───────────────────┐  │        │  ┌───────────────────┐  │
│  │ RC Insertion      │  │        │  │ Box Fields        │  │
│  │ Code Generation   │  │        │  │ RC Insertion      │  │
│  │ → Bytecode        │  │        │  │ Code Generation   │  │
│  └───────────────────┘  │        │  │ → Bytecode        │  │
└──────────┬──────────────┘        │  └───────────────────┘  │
           │                       └──────────┬──────────────┘
           ▼                                  ▼
┌─────────────────────────┐        ┌─────────────────────────┐
│     VM Execution        │        │    VM Execution         │
│  Witness + Aw, Bw, Cw   │        │  coeffs·A, coeffs·B,    │
│                         │        │  coeffs·C               │
└─────────────────────────┘        └─────────────────────────┘
```

## Key Concepts

### Taint Analysis

Noir (at the stage we integrate) does not distinguish between compile-time constants and runtime witness values. This distinction is critical for R1CS:

- **Pure values**: Constants that are the same across all executions → baked into R1CS matrix coefficients
- **Witness values**: Input-dependent values → placed in the witness vector

Taint analysis (`taint_analysis.rs`) propagates this information through the program. This matters for three reasons:

1. **Placement**: Pure values become matrix coefficients; Witness values become witness vector entries

2. **Control flow**: Branches must depend only on Pure values because the R1CS matrix *shape* is fixed at compile time. Different execution paths would require different numbers of constraints, which is impossible. The `untaint_control_flow.rs` pass transforms the program to ensure this.

3. **Operation lowering**: The same high-level operation compiles differently based on operand taints:
   - `Pure × Pure` → direct multiplication, result embedded in matrix
   - `Witness × Witness` → allocate fresh witness variable, emit constraint `a × b - result = 0`

   The **Explicit Witness pass** (`passes/explicit_witness.rs`) handles this lowering.

### Why Our Own SSA?

We convert Noir's SSA to our own representation (`compiler/ssa.rs`) because Noir's SSA uses extensive data sharing that complicates pass logic. Our SSA uses mostly immutable data structures, making transformations easier to reason about and implement - worth the trade-off for a codebase with 11+ compiler passes.

### Automatic Differentiation for Spartan

Spartan's sumcheck protocol requires computing random linear combinations of R1CS rows. We frame this as automatic differentiation:

- The constraint evaluation computes `f(w) = (coeffs · A · w, coeffs · B · w, coeffs · C · w)`
- The derivative `∂f/∂w = (coeffs · A, coeffs · B, coeffs · C)` is exactly the row linear combination

The AD compilation path transforms the program to compute these derivatives efficiently.

### BoxFields: Lazy Gradient Accumulation

The `BoxFields` pass (`passes/box_fields.rs`) optimizes AD by wrapping field values in heap-allocated boxes that accumulate their derivatives.

**Problem**: If expression `(a + b)` appears in multiple constraints with coefficients `c1, c2`, naive AD propagates separately:
- Add `c1` to `a`'s gradient, add `c1` to `b`'s gradient
- Add `c2` to `a`'s gradient, add `c2` to `b`'s gradient
- = 4 operations

**Solution**: Boxed values accumulate incoming gradients. On destruction (via GC), the combined gradient propagates once:
- Accumulate `c1 + c2` in the boxed `(a + b)` node
- On destruction: add `(c1 + c2)` to `a`, add `(c1 + c2)` to `b`
- = 2 propagation operations

This is lazy reverse-mode AD - gradient propagation is deferred until values are no longer needed.

### Lookups (Logup)

The `Lookup` and `DLookup` opcodes handle PLONK-style lookup constraints. We extend Spartan with the [logup argument](https://eprint.iacr.org/2022/1530) to support these. `Lookup` is used in witgen; `DLookup` computes the corresponding derivatives for AD.

## Directory Structure

```
src/
├── bin/main.rs              # CLI entry point
├── driver.rs                # Main compilation orchestration
├── project.rs               # Noir project loading (Nargo.toml, Prover.toml)
│
├── compiler/
│   ├── ssa.rs               # Core SSA data structure
│   ├── ssa_gen/             # Noir SSA → Spartan VM SSA conversion
│   │
│   ├── taint_analysis.rs    # Pure vs Witness classification
│   ├── monomorphization.rs  # Generic function specialization
│   ├── untaint_control_flow.rs  # Ensure branches are Pure
│   │
│   ├── r1cs_gen.rs          # SSA → R1CS constraint generation
│   │
│   ├── passes/              # Optimization and transformation passes
│   │   ├── mem2reg.rs       # Memory to register promotion
│   │   ├── cse.rs           # Common subexpression elimination
│   │   ├── dce.rs           # Dead code elimination
│   │   ├── explicit_witness.rs  # Taint-aware operation lowering
│   │   ├── box_fields.rs    # AD gradient boxing
│   │   ├── rc_insertion.rs  # Reference counting for memory management
│   │   └── ...
│   │
│   ├── codegen/             # SSA → Bytecode generation
│   ├── analysis/            # Type inference, liveness, etc.
│   └── flow_analysis.rs     # CFG construction, dominance, call graphs
│
└── vm/
    ├── bytecode.rs          # Bytecode definition and VM state
    ├── interpreter.rs       # Bytecode interpreter
    └── array.rs             # Array handling

opcode-gen/                  # Proc macro for bytecode opcode generation
ssa-builder/                 # Proc macro for SSA construction DSL
noir_examples/               # Test Noir programs
```

## Compiler Passes

Passes are orchestrated by `pass_manager.rs`. Key passes in approximate order:

| Pass | Purpose |
|------|---------|
| **Taint Analysis** | Classify values as Pure or Witness |
| **Monomorphization** | Specialize generic functions based on taints |
| **Untaint Control Flow** | Transform branches to depend only on Pure values |
| **Mem2Reg** | Promote memory operations to SSA registers |
| **CSE** | Eliminate common subexpressions |
| **Condition Propagation** | Propagate known conditions |
| **DCE** | Remove dead code |
| **Arithmetic Simplifier** | Algebraic simplifications |
| **Explicit Witness** | Lower operations based on operand taints |
| **Box Fields** | (AD only) Wrap fields for gradient accumulation |
| **RC Insertion** | Insert reference counting for heap memory |

## Runtime and VM

The bytecode VM (`vm/`) executes the generated witness and AD programs:

- **Field representation**: BN254 field elements as 4×u64 limbs (Montgomery form)
- **Memory model**: Stack frames with heap allocation for arrays
- **Memory management**: Reference counting (inserted by `rc_insertion.rs`)
- **60+ opcodes**: Field arithmetic, control flow, memory operations, R1CS constraints

Key opcodes:
- `R1C { a, b, c }` - Record constraint evaluation
- `WriteWitness { val }` - Output to witness vector
- `BumpD { matrix, var, sensitivity }` - (AD) Accumulate derivative contribution
- `Lookup` / `DLookup` - Lookup table operations

## Debug Output

Running with `--root=<noir_project>` produces debug files in `spartan_vm_debug/`:

- `initial_ssa.txt` - SSA after Noir conversion
- `untainted_ssa.txt` - SSA after monomorphization pipeline
- `a.txt`, `b.txt`, `c.txt` - R1CS matrix values
- `witgen_bytecode.txt` - Witness generation bytecode
- `ad_bytecode.txt` - AD bytecode
- CFG and call graph visualizations (with `--draw-graphs`)

## Dependencies

- **Noir compiler**: Custom branch at `reilabs/noir/tree/spartan-vm`
- **Field arithmetic**: `ark-bn254`, `ark-ff` (Arkworks)
- **Graphs**: `petgraph` for CFG/call graph analysis
