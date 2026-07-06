# eggy1

[中文文档](README_CN.md)

Simplifying infix arithmetic and bitwise expressions — including MBA-style
(mixed boolean-arithmetic) obfuscated expressions — via equality saturation
with [egglog-experimental](https://github.com/egraphs-good/egglog-experimental).

## Features

- **Expression Simplification**: Simplifies arithmetic/bitwise expressions using a large set of algebraic and MBA identities
- **MBA Deobfuscation**: Collapses mixed boolean-arithmetic identities such as `(x ^ y) + 2*(x & y) → x + y` and `(a & ~b) | (~a & b) → a ^ b`
- **Multiple Number Types**: Works over `i8/u8/i16/u16/i32/u32/i64/u64`, with all rules sound under **wrapping (modular)** arithmetic for the chosen width
- **Comprehensive Operator Support**: Arithmetic (`+`, `-`, `*`, `/`, `%`), bitwise (`&`, `|`, `^`, `~`, `<<`, `>>`), unary `-`/`~`, and the `mulhi(a, b)` high-multiply intrinsic
- **Flexible Output Formats**: Simplified expression, egglog rule/pattern form, or egglog expression form
- **Extract-and-Restart Driver**: Re-seeds a fresh e-graph with each round's best result, converging further than a single saturation pass while keeping the graph small

## Installation

### From Source

```bash
git clone <repository-url>
cd eggy1

# egglog-experimental is a git dependency, so the first build fetches and
# compiles it (this can take a while).
cargo install --path .
```

## Usage

### Basic Simplification

```bash
eggy1 "1 + 2 * 3"
# Output: 7

eggy1 "(a + b) * 0"
# Output: 0
```

### Command-line Options

```
Usage: eggy1 [OPTIONS] <EXPR>

Arguments:
  <EXPR>  The infix expression to simplify

Options:
  -r, --rule-compile                 Output expression in egglog format instead of simplifying
  -e, --expr-compile                 Output expression in egglog rule format instead of simplifying
  -n, --num-type <NUM_TYPE>          Numeric type to use [default: i64] [possible values: i64, u64, i32, u32, i16, u16, i8, u8]
  -i, --iter-limit <ITER_LIMIT>      Maximum number of simplification iterations [default: 10]
  -m, --max-restarts <MAX_RESTARTS>  Maximum number of extract-and-restart rounds [default: 2]
  -h, --help                         Print help
  -V, --version                      Print version
```

### Examples

#### Simplification

```bash
# Basic arithmetic
eggy1 "1 + 2 * 3"
# Output: 7

# With variables
eggy1 "x * 0 + y * 1"
# Output: y

# Bitwise operations
eggy1 "0x1 << 4"
# Output: 0x10

# Algebraic cancellation
eggy1 "((a + b) * (a - b)) - (a * a - b * b)"
# Output: 0
```

#### MBA Deobfuscation

The numeric type determines the bit width the rules are proven sound for. MBA
identities are most useful on a fixed width:

```bash
# XOR reconstruction
eggy1 -n i32 "(a & ~b) | (~a & b)"
# Output: (a ^ b)

# Boolean-arithmetic carry identity
eggy1 -n i32 "(x ^ y) + 2*(x & y)"
# Output: (x + y)
```

#### Rule / Pattern Form

Output the egglog rule (pattern) form, with bare pattern variables:

```bash
eggy1 -r "x * (y + z)"
# Output: (Mul x (Add y z))
```

#### Expression Form

Output the egglog expression form, with variables wrapped as `(Var "…")`:

```bash
eggy1 -e "a + b * c"
# Output: (Add (Var "a") (Mul (Var "b") (Var "c")))
```

#### Tuning the Search

`-i` controls how many rule-application iterations run per round; `-m` controls
how many extract-and-restart rounds run. Raise them for stubborn expressions:

```bash
eggy1 -i 30 -m 4 "very_complex_expression"
```

## How It Works

The tool uses [egglog-experimental](https://github.com/egraphs-good/egglog-experimental)
for equality saturation and term rewriting:

1. **Parsing**: A tokenizer + Pratt parser converts the infix expression to an
   egglog expression.
2. **Saturation**: A back-off scheduler runs the rule sets in phases
   (canonicalization → constant folding → analysis → identity/zero → directed
   MBA simplification).
3. **Extract-and-Restart**: The best term is extracted and used to re-seed a
   fresh e-graph; this repeats (up to `--max-restarts`) until a fixpoint, which
   lets later rounds resume from a smaller term with the full match budget.
4. **Extraction**: The minimal-size equivalent expression is extracted; constants
   with `|value| > 9` are printed in hex.

### Supported Simplification Rules

All rules are sound under wrapping (modular) arithmetic for every supported
width, or are gated on the numeric type / a guard predicate.

- Constant folding (e.g. `1 + 2 → 3`)
- Identity / zero / absorption (e.g. `x + 0 → x`, `x * 1 → x`, `x & ~x → 0`)
- Neg/Not canonicalization and De Morgan laws
- Distributivity and term collection (e.g. `2*a + 3*a → 5*a`)
- MBA identities (Hacker's Delight): XOR/OR/AND reconstruction, carry
  identities, the three-input full adder, annihilation / opaque-predicate
  collapse, etc.
- Shift algebra: shift combining and distribution over bitwise ops / `+` / `-`
- Magic-number division recognition (rewrites compiler-emitted
  multiply-high sequences back to `n / d`)

## Development

### Project Structure

```
src/
├── lib.rs           # Rule definitions (make_egg), egglog primitives, simplify driver
├── main.rs          # Thin CLI binary over the library
└── expr_convert.rs  # Expression parsing and format conversion
tests/
├── expr_convert_tests.rs  # Parser / converter unit tests
└── simplify_tests.rs      # Simplification & magic-number tests (grouped for parallelism)
Cargo.toml           # Project configuration and dependencies
```

### Building from Source

```bash
cargo build --release   # optimized build
cargo test              # run all tests (integration tests run in parallel)
cargo run -- "1 + 2"    # run against an expression
```

### Adding New Rules

Simplification rules are defined in `src/lib.rs` in the `make_egg` function.
To add a new rule:

1. Add it with the `rewrite!` macro to the appropriate rule set. Prefer
   directed `=>` rules in `simplify`; use `<=>` (birewrite) only for genuine
   normalization identities, since birewrites grow the e-graph fast.
2. Ensure it is sound under wrapping arithmetic for **all** supported widths, or
   gate it on `num_type` / a guard primitive (e.g. `is-2-pow-n-*`).
3. Add cases to `tests/simplify_tests.rs`. Because extraction may pick any of
   several equivalent minimal forms, the expected value is a set of acceptable
   outputs; constants ≥ 10 appear in hex.

**Adding a new numeric type** additionally requires a primitive for every op in
`init_egg_function`, plus adding the type to the `value_parser` list in `Cli`.

## Testing

```bash
# Run all tests
cargo test

# Run a single integration binary
cargo test --test expr_convert_tests
cargo test --test simplify_tests
```

Test cases cover arithmetic and bitwise simplification, MBA identities,
magic-number division recognition, wrapping-arithmetic soundness regressions,
and the parser/converter.

## Limitations

- Integer arithmetic only (no floating-point).
- Expression size is limited by available memory.
- Very complex expressions may not converge within the iteration / restart limits.

## License

This project is licensed under the terms of the MIT license.

## Acknowledgments

- Built with [egglog-experimental](https://github.com/egraphs-good/egglog-experimental)
- Uses [clap](https://github.com/clap-rs/clap) for command-line argument parsing
- MBA identities drawn from *Hacker's Delight* and equality-saturation MBA research

---

**Note**: This tool is primarily designed for educational and research purposes,
demonstrating how equality saturation can be applied to algebraic simplification
and MBA deobfuscation.
