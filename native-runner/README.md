# Native Runner for Spartan VM

A Rust-based runner for executing LLVM-compiled Spartan VM programs natively.

## Overview

The native-runner executes compiled Noir programs by:
1. Taking a compiled object file (`.o`)
2. Reading inputs from `Prover.toml`
3. Linking the object file into a shared library
4. Loading and executing `spartan_main` with the inputs
5. Collecting witnesses and constraints

## Building

```bash
cd /path/to/workspace
cargo build --release -p native-runner
```

This produces `target/release/native-runner`.

## Prerequisites

Before running, you need:
1. **Spartan VM** - to compile Noir programs to object files
2. **Runtime library** - `libspartan_wasm_runtime.so` for field arithmetic

Build both with:
```bash
LLVM_SYS_211_PREFIX=/usr/lib/llvm-21 cargo build --release
cd wasm-runtime && cargo build --release
```

## Usage

### Basic Usage

```bash
# Compile a Noir program to an object file
LLVM_SYS_211_PREFIX=/usr/lib/llvm-21 ./target/release/spartan-vm \
    --root noir_tests/power \
    --emit-object /tmp/power.o

# Run with native-runner
LD_LIBRARY_PATH=target/release ./target/release/native-runner /tmp/power.o \
    -i noir_tests/power/Prover.toml \
    -r target/release/libspartan_wasm_runtime.so
```

### Command Line Options

```
Usage: native-runner [OPTIONS] <OBJECT_FILE>

Arguments:
  <OBJECT_FILE>  Path to the compiled object file (.o)

Options:
  -i, --input <PATH>           Path to Prover.toml
  -o, --output <PATH>          Path to output JSON file
  -r, --runtime <PATH>         Path to libspartan_wasm_runtime.so
      --witness-count <N>      Number of witnesses to allocate (default: 1000003)
      --constraint-count <N>   Number of constraints to allocate (default: 1000001)
  -v, --verbose                Print verbose output
  -h, --help                   Print help
```

### Examples

**Simple addition (just_add):**
```bash
# Compile
./target/release/spartan-vm --root noir_tests/just_add --emit-object /tmp/just_add.o

# Run
LD_LIBRARY_PATH=target/release ./target/release/native-runner /tmp/just_add.o \
    -i noir_tests/just_add/Prover.toml \
    -r target/release/libspartan_wasm_runtime.so \
    -v
```

Output:
```
Object file: /tmp/just_add.o
Prover.toml: noir_tests/just_add/Prover.toml
Loaded 3 inputs from Prover.toml
  x = 2
  y = 3
  z = 5
Converted to 3 field elements
...
Execution complete!
  Witnesses: 0
  Constraints: 1
```

**Power example (1M iterations):**
```bash
# Compile
./target/release/spartan-vm --root noir_tests/power --emit-object /tmp/power.o

# Run
LD_LIBRARY_PATH=target/release ./target/release/native-runner /tmp/power.o \
    -i noir_tests/power/Prover.toml \
    -r target/release/libspartan_wasm_runtime.so \
    -v
```

Output:
```
Loaded 2 inputs from Prover.toml
  x = 2
  y = 11576989127771471539585320265679834540101776824219102960197490114445753948512
...
Execution complete!
  Witnesses: 1000000
  Constraints: 1000001
```

### Output Format

With `-o output.json`, the runner produces:
```json
{
  "witness_count": 1000000,
  "constraint_count": 1000001,
  "witnesses": ["0", "2", "4", ...],
  "constraints": {
    "a": ["0x...", ...],
    "b": ["0x...", ...],
    "c": ["0x...", ...]
  }
}
```

## Prover.toml Format

The `Prover.toml` file contains input values for the Noir program:

```toml
x = "2"                    # String decimal
y = 42                     # Integer
arr = [1, 2, 3]            # Array (expands to arr[0], arr[1], arr[2])
big = "12345678901234567890123456789"  # Large decimal
hex = "0x1234abcd"         # Hex value
```

Values are automatically converted to BN254 field elements in Montgomery form.

## Troubleshooting

### `undefined symbol: __write_witness`
The native-runner binary must export its symbols. This is handled automatically by the build script (`build.rs`).

### `libspartan_wasm_runtime.so: cannot open shared object file`
Set `LD_LIBRARY_PATH` to include the directory containing the runtime library:
```bash
LD_LIBRARY_PATH=target/release ./target/release/native-runner ...
```

### Linker errors
Ensure you have a C compiler (`cc`) installed and in your PATH.

### macOS version mismatch warning
If you see a warning like:
```
ld: warning: object file was built for newer macOS version (X.X) than being linked (Y.Y)
```

Set the `MACOSX_DEPLOYMENT_TARGET` environment variable when compiling:
```bash
# Compile with explicit deployment target
MACOSX_DEPLOYMENT_TARGET=11.0 LLVM_SYS_211_PREFIX=/path/to/llvm ./target/release/spartan-vm \
    --root noir_tests/power --emit-object /tmp/power.o
```

This ensures both the object file and linker use the same macOS version.

### Buffer too small
If you get crashes with large programs, increase buffer sizes:
```bash
./target/release/native-runner program.o --witness-count 2000000 --constraint-count 2000001
```

## Architecture

```
┌─────────────────┐
│  Prover.toml    │  Input values (decimal strings)
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  native-runner  │  Parse TOML, convert to Montgomery form
└────────┬────────┘
         │
         ├──────────────────────────┐
         ▼                          ▼
┌─────────────────┐        ┌─────────────────┐
│   program.o     │        │ runtime.so      │
│ (LLVM compiled) │        │ (field ops)     │
└────────┬────────┘        └────────┬────────┘
         │                          │
         └──────────┬───────────────┘
                    ▼
            ┌───────────────┐
            │  program.so   │  Linked shared library
            └───────┬───────┘
                    │
                    ▼
            ┌───────────────┐
            │ spartan_main  │  Called via dlopen/dlsym
            └───────┬───────┘
                    │
                    ▼
            ┌───────────────┐
            │   Results     │  Witnesses & constraints
            └───────────────┘
```

