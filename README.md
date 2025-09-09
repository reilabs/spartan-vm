Spartan VM project

Noir code -> R1CS and witness

## How to run

```
RUST_LOG=info RUST_BACKTRACE=1 cargo run --release -- --root=noir_examples/power --public-witness 1 2 3 5
```

## CLI flags

# Mandatory
- **--root PATH**: The root directory of the Noir project to run.
  - Example: `--root noir_examples/power`

- **--public-witness <VALUES>...**: Zero or more public witness values.
     Values should be field elements parseable for BN254 (e.g., decimal integers)
  - Example: `--public-witness 1 2 3 5`

# Optional
