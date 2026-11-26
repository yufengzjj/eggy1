# eggy1

[English](README.md)

在固定位宽的回绕算术下化简含算术和位运算的整数表达式，主要针对 MBA（混合布尔-算术）混淆表达式。它把线性、半线性和多项式 MBA 的代数重建与 [egglog-experimental](https://github.com/egraphs-good/egglog-experimental) 的等式饱和结合起来。

## 示例

| 命令 | 输出 |
|---|---|
| `eggy1 -n i32 "(x ^ y) + 2*(x & y)"` | `(x + y)` |
| `eggy1 -n u32 "2*(x \| y) - (x & ~y) - (~x & y)"` | `(x + y)` |
| `eggy1 -n u32 "(x & 0xf0) + (x & 0x0f)"` | `(x & 0xff)` |
| `eggy1 -n u32 "(x & y)*(x \| y) + (x & ~y)*(~x & y)"` | `(x * y)` |
| `eggy1 -n u32 "(x \| 0x10)*(x & 0x10) + (x & ~0x10)*(~x & 0x10)"` | `(0x10 * x)` |
| `eggy1 -n u32 "x - ((2*x) \| ~(2*0x1234)) - 0x1234 - 1"` | `(x ^ 0x1234)` |
| `eggy1 -n u32 "mulhi(x, 0xaaaaaaab) >> 1"` | `(x / 3)` |
| `eggy1 -n u8 "(x*(x+3)+2) & 1"` | `0` |

绝对值大于 9 的常数以十六进制输出。在 PowerShell 里要给表达式加引号；表达式以 `-` 开头时，在它前面写 `--`（`eggy1 -n i32 -- "-x + y"`）。

## 安装

```bash
git clone <repository-url>
cd eggy1
cargo install --path .   # 第一次构建会下载并编译 egglog-experimental
```

## 用法

```
Usage: eggy1 [OPTIONS] [EXPR]

  -n, --num-type <NUM_TYPE>          i64（默认）、u64、i32、u32、i16、u16、i8、u8
  -i, --iter-limit <ITER_LIMIT>      每轮 egglog 的规则迭代次数 [默认: 10]
  -m, --max-restarts <MAX_RESTARTS>  提取再重启的轮数 [默认: 2]
      --trace                        把预处理候选和每轮大小打印到 stderr
      --stats                        把各 pass 的次数、耗时和胜出次数打印到 stderr
      --passes <PASSES>              修改 pass 管线（见下文）
      --show-passes                  打印 pass 管线后退出
```

运算符：`+ - * / % & | ^ ~ << >>`、一元 `-`，以及 `mulhi(a, b)`（乘积的高半部分）。常数可以是十进制或十六进制（`0xff`）。结果在所选位宽下总与输入等价；只对部分类型成立的规则只在那些类型上使用。

## 工作原理

1. **预处理。** 把输入分成线性区域（叶子的位运算函数乘以常数再相加），每个区域按它的取值重建：线性 MBA 用 SiMBA 式的方法，带常数掩码的区域（半线性）逐位处理，多项式 MBA 用 GAMBA 式的展开和因式分解。其他 pass 处理已知的混淆手法：已知位推理（`lowbits`）、小 T-函数查表（`tfunc`）、按单个位分情况（`split_bits`）、`2^k·a + c` 形式操作数的拆半（`halve`）等。保留多个重建候选。
2. **等式饱和。** 把候选合并到一个 e-graph 里，运行各规则集（规范化、常量折叠、分析、恒等式、有向 MBA 规则、魔数除法识别）。提取最小的项，下一轮在新的 e-graph 上从它开始，直到不再变化。枚举证明为最小的重建结果跳过饱和。
3. **收尾（polish）。** 对结果做局部改写（把 `~` 往里推、合并常数、提公因式），只保留让项变小的改写。

这些步骤的顺序是用一门小语言写的管线，从 `src/default.pipe` 读入；`--show-passes` 打印它。

## 修改管线

`--passes` 接受若干项，依次作用在默认设置之上：

```bash
eggy1 --passes "extra=0 keep=1" -n u32 "expr"            # 设置
eggy1 --passes "off=relate,poly_mba" -n u32 "expr"        # 关掉内部 pass
eggy1 --passes "prepass=lowbits | (if mixed rewrite)" "expr"
eggy1 --passes "file=my.pipe" "expr"                      # 从文件读入各项
```

管线把一组等价候选映射为另一组：`a | b` 依次执行，还有 `(union a b)`、`(best K a b)`、`(first a b)`、`(fix N p)`、`(if COND a b)`、`(with off=NAME p)`、寄存器 `(save R)`/`(load R)`、`(mul >= 4 && !mixed)` 这样的条件，以及 `(let NAME p)` 定义（`src/default.pipe` 里定义的名字可以直接用）。读入时会检查管线（未知名字、参数不对、寄存器先读后存、pass 出现在不能运行它的管线里、递归），不起作用的部分给出警告。完整的参考（所有形式、pass、条件、设置和限值）见 [docs/pipe-language.md](docs/pipe-language.md)。

## Benchmark 与 fuzz

```bash
sh scripts/fetch-datasets.sh                                       # 把 MBA 数据集下载到 bench-data/
cargo run --release --example bench -- -l 100 bench-data/*.txt     # 每节 100 个用例
python -I scripts/bench-shards.py -j 26 -o out/quick --cases scripts/quick-cases.tsv   # 精简集，并行分片
python -I scripts/bench-diff.py out/old out/new --show             # 比较两次运行
cargo run --release --example fuzz -- -c 20000 -j 13 -o fails.txt  # 差分 fuzz
```

benchmark 用求值检查每个输出与输入等价，并按节统计：达到数据集参考答案大小的（`solved`）、变小的（`partial`）、没变的、超时的、错误的。`scripts/gen-*.py` 生成更多用例集（半线性、更深的、移位和除法）。

## 开发

```bash
cargo build
cargo test -- --test-threads=8              # 全部测试（几分钟）
cargo test --test simplify_tests complex_   # 一组化简测试
cargo test --lib                            # 单元测试
```

| 路径 | 内容 |
|---|---|
| `src/lib.rs` | egglog 规则（`make_egg`）、原语、命令行、驱动 |
| `src/sched.rs`、`src/pipe.rs`、`src/pipe_lang.rs`、`src/default.pipe` | 管线设置、执行器、语言、默认管线 |
| `src/linear_mba/` | 线性与半线性重建、宽区域、`relate`、`halve`、`split_bits`、polish |
| `src/poly_mba.rs` | 多项式 MBA 的展开与因式分解 |
| `src/lowbits.rs`、`src/known_bits.rs` | 已知位推理 |
| `src/tfunc.rs` | 小表达式查表，用 T-函数精确证明等价 |
| `src/minimal.rs` | 用枚举证明最小 |
| `src/expr_convert.rs`、`src/eval.rs`、`src/dag.rs` | 解析与输出、求值、共享子项 |
| `examples/bench.rs`、`examples/fuzz.rs`、`scripts/` | benchmark、fuzzer、用例生成和运行工具 |

新规则用 `rewrite!` 宏加在 `make_egg` 里，模式用中缀写法。规则必须在每种支持的位宽下对回绕算术成立，否则要按类型或守卫原语限定；新增数值类型需要补齐所有按类型区分的原语，并加进 `--num-type` 的取值列表。化简测试接受一组输出，因为可能提取出几个大小相同的形式。

## 局限

- 只支持 8 到 64 位整数。
- 线性区域最多 6 个叶子时能精确重建；更宽的只能拆成小组重建，所以很宽的 MBA 可能只化简一部分。
- 很大或嵌套很深的输入可能要几秒；`--passes time_limit=MS` 限制运行时间（MS 毫秒后不再开始新的 pass，输出到那时最小的形式）。

## 许可

MIT。

## 致谢

基于 [egglog-experimental](https://github.com/egraphs-good/egglog-experimental) 和 [clap](https://github.com/clap-rs/clap)。方法参考 *Hacker's Delight* 以及已发表的 MBA 化简工作（SiMBA、GAMBA 等）。
