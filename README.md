# eggy1

[中文文档](README_CN.md)

A Rust command-line tool for simplifying infix arithmetic expressions using egglog-based rewriting.

## Features

- **Expression Simplification**: Simplifies arithmetic expressions using algebraic rules
- **Multiple Number Types**: Supports different numeric types (default: i64)
- **Comprehensive Operator Support**: Handles arithmetic (`+`, `-`, `*`, `/`, `%`), bitwise (`&`, `|`, `^`, `~`, `<<`, `>>`), and parentheses
- **Flexible Output Formats**: Can output simplified expressions, egglog rule format, or compiled expression format
- **Customizable Iteration Limits**: Control the simplification depth with configurable iteration limits

## Installation

### From Source

```bash
# Clone the repository
git clone <repository-url>
cd eggy1

# Build and install
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
Usage: eggy1.exe [OPTIONS] <EXPR>

Arguments:
  <EXPR>  The infix expression to simplify

Options:
  -r, --rule-compile             Output expression in egglog format instead of simplifying
  -e, --expr-compile             Output expression in egglog rule format instead of simplifying
  -n, --num-type <NUM_TYPE>      Numeric type to use [default: i64] [possible values: i64, u64, i32, u32, i16, u16, i8, u8]
  -i, --iter-limit <ITER_LIMIT>  Maximum number of simplification iterations [default: 30]
  -h, --help                     Print help
  -V, --version                  Print version
```

### Examples

#### Simplification Examples

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

# Complex expression
eggy1 "((a + b) * (a - b)) - (a * a - b * b)"
# Output: 0
```

#### Rule Compilation Mode

Generate egglog rules for an expression:

```bash
eggy1 -r "x * (y + z)"
# Output: (Mul x (Add y z))
```

#### Expression Compilation Mode

Output the expression in compiled format:

```bash
eggy1 -e "a + b * c"
# Output: (Add (Var "a") (Mul (Var "b") (Var "c")))
```

#### Adjust Iteration Limit

Control simplification depth:

```bash
eggy1 -i 100 "very_complex_expression"
```

## How It Works

The tool uses [egglog-experimental](https://github.com/egraphs-good/egglog-experimental) for equality saturation and term rewriting. The simplification process involves:

1. **Parsing**: Convert infix expressions to abstract syntax trees
2. **Rule Application**: Apply algebraic simplification rules using egglog
3. **Extraction**: Extract the simplest equivalent expression from the e-graph

### Supported Simplification Rules

- Constant folding (e.g., `1 + 2 → 3`)
- Identity and zero element elimination (e.g., `x + 0 → x`, `x * 1 → x`)
- Algebraic canonicalization
- Bitwise operation simplification
- Arithmetic simplification

## Development

### Project Structure

```
src/
├── main.rs          # CLI interface and main simplification logic
├── expr_convert.rs  # Expression parsing and conversion utilities
Cargo.toml          # Project configuration and dependencies
```

### Building from Source

```bash
# Build the project
cargo build --release

# Run tests
cargo test

# Run with debug output
cargo run -- "1 + 2"
```

### Adding New Rules

The simplification rules are defined in `main.rs` in the `make_egg` function. To add new rules:

1. Add the rule to the appropriate rule set in `make_egg`
2. Ensure the rule preserves equivalence
3. Test with various expressions to verify correctness

## Testing

The project includes comprehensive tests for expression simplification:

```bash
# Run all tests
cargo test

# Run specific test modules
cargo test expr_convert
cargo test simplify
```

Test cases cover:
- Basic arithmetic operations
- Bitwise operations
- Variable handling
- Edge cases and error conditions

## Performance Considerations

- The default iteration limit (30) balances thoroughness and performance
- Complex expressions with many variables may require higher iteration limits
- The tool uses egglog's efficient e-graph data structures for rule application

## Limitations

- Currently supports integer arithmetic only (no floating-point)
- Expression size is limited by available memory
- Very complex expressions may not converge within iteration limits

## Contributing

Contributions are welcome! Please feel free to submit pull requests for:
- New simplification rules
- Performance improvements
- Additional expression types
- Bug fixes
- Documentation improvements

## License

This project is licensed under the terms of the MIT license.

## Acknowledgments

- Built with [egglog-experimental](https://github.com/egraphs-good/egglog-experimental)
- Uses [clap](https://github.com/clap-rs/clap) for command-line argument parsing
- Inspired by algebraic simplification and term rewriting research

## Support

For issues, questions, or feature requests, please:
1. Check the existing test cases for similar functionality
2. Review the command-line help (`eggy1 --help`)
3. Open an issue on the project repository

---

**Note**: This tool is primarily designed for educational and demonstration purposes, showing how egglog can be used for algebraic simplification in practice.