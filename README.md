# eggy1

[中文文档](README_CN.md)

Simplifies integer expressions with arithmetic and bitwise operators, in particular
MBA-style (mixed boolean-arithmetic) obfuscated ones, under wrapping arithmetic of a fixed
width. It combines algebraic rebuilds of linear, semi-linear and polynomial MBA with
equality saturation in [egglog-experimental](https://github.com/egraphs-good/egglog-experimental).

## Examples

| Command | Output |
|---|---|
| `eggy1 -n i32 "(x ^ y) + 2*(x & y)"` | `(x + y)` |
| `eggy1 -n u32 "2*(x \| y) - (x & ~y) - (~x & y)"` | `(x + y)` |
| `eggy1 -n u32 "(x & 0xf0) + (x & 0x0f)"` | `(x & 0xff)` |
| `eggy1 -n u32 "(x & y)*(x \| y) + (x & ~y)*(~x & y)"` | `(x * y)` |
| `eggy1 -n u32 "(x \| 0x10)*(x & 0x10) + (x & ~0x10)*(~x & 0x10)"` | `(0x10 * x)` |
| `eggy1 -n u32 "x - ((2*x) \| ~(2*0x1234)) - 0x1234 - 1"` | `(x ^ 0x1234)` |
| `eggy1 -n u32 "mulhi(x, 0xaaaaaaab) >> 1"` | `(x / 3)` |
| `eggy1 -n u8 "(x*(x+3)+2) & 1"` | `0` |

Constants with absolute value above 9 are printed in hex. In PowerShell, quote the
expression; when it starts with `-`, put `--` before it (`eggy1 -n i32 -- "-x + y"`).

## Installation

```bash
git clone <repository-url>
cd eggy1
cargo install --path .   # the first build fetches and compiles egglog-experimental
```

## Usage

```
Usage: eggy1 [OPTIONS] [EXPR]

  -n, --num-type <NUM_TYPE>          i64 (default), u64, i32, u32, i16, u16, i8, u8
  -i, --iter-limit <ITER_LIMIT>      Rule iterations per egglog round [default: 10]
  -m, --max-restarts <MAX_RESTARTS>  Extract-and-restart rounds [default: 2]
      --time-limit <SECONDS>         Stop starting passes after this long, print the smallest form so far
      --trace                        Print pre-pass candidates and round sizes to stderr
      --stats                        Print per-pass counts, times and wins to stderr
      --passes <PASSES>              Change the pass pipeline (see below)
      --show-passes                  Print the pass pipeline and exit
```

Operators: `+ - * / % & | ^ ~ << >>`, unary `-`, and `mulhi(a, b)` (the high half of the
product). Literals may be decimal or hex (`0xff`). Every result is equivalent to the input
for the chosen width; rules that hold only for some types are applied only there.

## How it works

1. **Pre-pass.** The input is cut into linear regions (constant multiples of bitwise
   functions of leaves) and each region is rebuilt from its values: SiMBA-style for linear
   MBA, bit by bit for regions with constant masks (semi-linear), and GAMBA-style expansion
   and factoring for polynomial MBA. Other passes undo known obfuscations: known-bit
   reasoning (`lowbits`), small T-function lookup (`tfunc`), case splits on single bits
   (`split_bits`), halving of `2^k·a + c` operands (`halve`), and more. Several rebuilt
   candidates are kept.
2. **Equality saturation.** The candidates are unioned in an e-graph and the rule sets run
   (canonicalization, constant folding, analyses, identities, directed MBA rules,
   magic-number division recognition). The smallest term is extracted, and the next round
   starts from it on a fresh e-graph, until nothing changes. A rebuild proved minimal by
   enumeration skips saturation.
3. **Polish.** Local rewrites on the result (pushing `~` inward, joining constants,
   factoring), each kept only when it makes the term smaller.

The order of these steps is a pipeline written in a small language and read from
`src/default.pipe`; `--show-passes` prints it.

## Changing the pipeline

`--passes` takes items applied on top of the defaults:

```bash
eggy1 --passes "extra=0 keep=1" -n u32 "expr"            # settings
eggy1 --passes "off=relate,poly_mba" -n u32 "expr"        # turn inner passes off
eggy1 --passes "prepass=lowbits | (if mixed rewrite)" "expr"
eggy1 --passes "file=my.pipe" "expr"                      # items from a file
```

A pipeline maps a list of equivalent candidates to another: `a | b` runs in sequence,
`(union a b)`, `(best K a b)`, `(first a b)`, `(fix N p)`, `(if COND a b)`, `(with off=NAME p)`,
`(save R)`/`(load R)` registers, conditions such as `(mul >= 4 && !mixed)`, and
`(let NAME p)` definitions (those of `src/default.pipe` can be reused). Pipelines are checked
when read (unknown names, wrong arguments, register reads before any save, passes outside the
pipeline that can run them, recursion), and parts that do nothing give warnings. The full
reference, with every form, pass, condition, setting and limit, is
[docs/pipe-language.md](docs/pipe-language.md) (in Chinese).

## Benchmarks and fuzzing

```bash
sh scripts/fetch-datasets.sh                                       # MBA datasets into bench-data/
cargo run --release --example bench -- -l 100 bench-data/*.txt     # 100 cases per section
python -I scripts/bench-shards.py -j 26 -o out/quick --cases scripts/quick-cases.tsv   # quick set, in parallel shards
python -I scripts/bench-diff.py out/old out/new --show             # compare two runs
cargo run --release --example fuzz -- -c 20000 -j 13 -o fails.txt  # differential fuzzer
```

The benchmark checks every output against its input by evaluation and reports per
section how many cases reach the dataset's ground-truth size (`solved`), get smaller
(`partial`), stay unchanged, time out, or are wrong. `scripts/gen-*.py` generate further
case sets (semi-linear, deeper, shifts and division).

## Development

```bash
cargo build
cargo test -- --test-threads=8              # all tests (a few minutes)
cargo test --test simplify_tests complex_   # one group of simplification tests
cargo test --lib                            # unit tests
```

| Path | Contents |
|---|---|
| `src/lib.rs` | egglog rules (`make_egg`), primitives, CLI, driver |
| `src/sched.rs`, `src/pipe.rs`, `src/pipe_lang.rs`, `src/default.pipe` | pipeline settings, executor, language, defaults |
| `src/linear_mba/` | linear and semi-linear rebuilds, wide regions, `relate`, `halve`, `split_bits`, polish |
| `src/poly_mba.rs` | polynomial MBA expansion and factoring |
| `src/lowbits.rs`, `src/known_bits.rs` | known-bits reasoning |
| `src/tfunc.rs` | small-expression lookup with exact T-function proofs |
| `src/minimal.rs` | minimality proofs by enumeration |
| `src/expr_convert.rs`, `src/eval.rs`, `src/dag.rs` | parsing and printing, evaluation, shared subterms |
| `examples/bench.rs`, `examples/fuzz.rs`, `scripts/` | benchmark, fuzzer, case generators and run tools |

New rules go in `make_egg` with the `rewrite!` macro, which takes infix patterns. A rule
must be sound under wrapping arithmetic for every supported width or be gated on the type
or a guard primitive; adding a numeric type needs every per-type primitive and an entry in
the `--num-type` value list. Simplification tests accept a set of outputs, since several
forms of equal size can be extracted.

## Limitations

- Integers of 8 to 64 bits only.
- Linear regions are rebuilt exactly up to 6 leaves; wider ones only by splitting into
  smaller groups, so wide MBA can stay partly simplified.
- Large or deeply nested inputs can take seconds; use `--time-limit` to bound the run.

## License

MIT.

## Acknowledgments

Built on [egglog-experimental](https://github.com/egraphs-good/egglog-experimental) and
[clap](https://github.com/clap-rs/clap). Methods follow *Hacker's Delight* and published MBA
simplification work (SiMBA, GAMBA and others).
