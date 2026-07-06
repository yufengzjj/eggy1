# eggy1

[English](README.md)

一个基于 egglog 等式饱和的 Rust 命令行工具，用于简化中缀算术与位运算表达式，
包括 MBA（混合布尔-算术，mixed boolean-arithmetic）风格的混淆表达式。

## 功能特性

- **表达式简化**：使用大量代数与 MBA 恒等式简化算术/位运算表达式
- **MBA 反混淆**：折叠混合布尔-算术恒等式，例如 `(x ^ y) + 2*(x & y) → x + y`、`(a & ~b) | (~a & b) → a ^ b`
- **多数字类型支持**：支持 `i8/u8/i16/u16/i32/u32/i64/u64`，所有规则在所选位宽的 **wrapping（模）** 算术下都可靠
- **完整的运算符支持**：算术（`+`, `-`, `*`, `/`, `%`）、位运算（`&`, `|`, `^`, `~`, `<<`, `>>`）、一元 `-`/`~`，以及 `mulhi(a, b)` 高位乘法内建
- **灵活的输出格式**：简化后的表达式、egglog 规则/模式形式，或 egglog 表达式形式
- **提取-重启驱动**：每轮用当前最优结果重建一个干净的 e-graph，比单次饱和收敛得更彻底，同时抑制图膨胀

## 安装

### 从源码安装

```bash
git clone <repository-url>
cd eggy1

# egglog-experimental 是 git 依赖，首次构建会拉取并编译它（耗时较长）。
cargo install --path .
```

## 使用方法

### 基本简化

```bash
eggy1 "1 + 2 * 3"
# 输出: 7

eggy1 "(a + b) * 0"
# 输出: 0
```

### 命令行选项

```
Usage: eggy1 [OPTIONS] <EXPR>

Arguments:
  <EXPR>  要简化的中缀表达式

Options:
  -r, --rule-compile                 输出表达式的 egglog 规则（模式）形式而不是简化
  -e, --expr-compile                 输出表达式的 egglog 表达式形式而不是简化
  -n, --num-type <NUM_TYPE>          使用的数字类型 [默认值: i64] [可能的取值: i64, u64, i32, u32, i16, u16, i8, u8]
  -i, --iter-limit <ITER_LIMIT>      最大简化迭代次数 [默认值: 10]
  -m, --max-restarts <MAX_RESTARTS>  最大提取-重启轮数 [默认值: 2]
  -h, --help                         打印帮助信息
  -V, --version                      打印版本信息
```

### 示例

#### 简化

```bash
# 基础算术
eggy1 "1 + 2 * 3"
# 输出: 7

# 包含变量
eggy1 "x * 0 + y * 1"
# 输出: y

# 位运算
eggy1 "0x1 << 4"
# 输出: 0x10

# 代数消去
eggy1 "((a + b) * (a - b)) - (a * a - b * b)"
# 输出: 0
```

#### MBA 反混淆

数字类型决定规则在哪个位宽下被证明可靠。MBA 恒等式在固定位宽下最有用：

```bash
# XOR 重构
eggy1 -n i32 "(a & ~b) | (~a & b)"
# 输出: (a ^ b)

# 布尔-算术进位恒等式
eggy1 -n i32 "(x ^ y) + 2*(x & y)"
# 输出: (x + y)
```

#### 规则/模式形式

输出 egglog 规则（模式）形式，变量为裸模式变量：

```bash
eggy1 -r "x * (y + z)"
# 输出: (Mul x (Add y z))
```

#### 表达式形式

输出 egglog 表达式形式，变量被包裹为 `(Var "…")`：

```bash
eggy1 -e "a + b * c"
# 输出: (Add (Var "a") (Mul (Var "b") (Var "c")))
```

#### 调整搜索强度

`-i` 控制每轮运行多少次规则应用迭代；`-m` 控制运行多少轮提取-重启。
遇到顽固表达式可调高：

```bash
eggy1 -i 30 -m 4 "very_complex_expression"
```

## 工作原理

该工具使用 [egglog-experimental](https://github.com/egraphs-good/egglog-experimental)
进行等式饱和与项重写：

1. **解析**：分词器 + Pratt 解析器将中缀表达式转换为 egglog 表达式。
2. **饱和**：back-off 调度器分阶段运行各规则集（规范化 → 常量折叠 → 分析 →
   恒等/零元 → 定向 MBA 简化）。
3. **提取-重启**：提取当前最优项，用它重建一个干净的 e-graph 再次运行；如此
   重复（至多 `--max-restarts` 轮）直到不动点，使后续轮次从更小的项、以完整的
   匹配预算继续重写。
4. **提取**：提取最小规模的等价表达式；`|值| > 9` 的常量以十六进制打印。

### 支持的简化规则

所有规则在每个支持的位宽下都在 wrapping（模）算术下可靠，或按数字类型/守卫
谓词进行门控。

- 常量折叠（例如 `1 + 2 → 3`）
- 恒等/零元/吸收律（例如 `x + 0 → x`, `x * 1 → x`, `x & ~x → 0`）
- Neg/Not 规范化与德摩根律
- 分配律与同类项合并（例如 `2*a + 3*a → 5*a`）
- MBA 恒等式（Hacker's Delight）：XOR/OR/AND 重构、进位恒等式、三输入全加器、
  湮灭/不透明谓词折叠等
- 移位代数：移位合并，以及移位对位运算 / `+` / `-` 的分配
- Magic-number 除法识别（把编译器生成的高位乘法序列还原为 `n / d`）

## 开发

### 项目结构

```
src/
├── lib.rs           # 规则定义（make_egg）、egglog 原语、simplify 驱动
├── main.rs          # 基于库的轻量 CLI 二进制
└── expr_convert.rs  # 表达式解析与格式转换
tests/
├── expr_convert_tests.rs  # 解析器/转换器单元测试
└── simplify_tests.rs      # 简化与 magic-number 测试（按规则分组以便并行）
Cargo.toml           # 项目配置与依赖
```

### 从源码构建

```bash
cargo build --release   # 优化构建
cargo test              # 运行所有测试（集成测试并行运行）
cargo run -- "1 + 2"    # 对表达式运行
```

### 添加新规则

简化规则在 `src/lib.rs` 的 `make_egg` 函数中定义。要添加新规则：

1. 用 `rewrite!` 宏把规则加到合适的规则集。优先在 `simplify` 里用定向 `=>` 规则；
   只在真正的规范化恒等式上使用 `<=>`（birewrite），因为 birewrite 会让 e-graph
   快速膨胀。
2. 确保规则在**所有**支持的位宽下都在 wrapping 算术下可靠，否则按 `num_type` /
   守卫原语（如 `is-2-pow-n-*`）进行门控。
3. 在 `tests/simplify_tests.rs` 添加用例。由于提取可能选中多个等价最小形式之一，
   期望值是一组可接受的输出；≥ 10 的常量以十六进制显示。

**添加新的数字类型**还需要在 `init_egg_function` 中为每个运算添加原语，并把该
类型加入 `Cli` 的 `value_parser` 列表。

## 测试

```bash
# 运行所有测试
cargo test

# 运行单个集成测试二进制
cargo test --test expr_convert_tests
cargo test --test simplify_tests
```

测试用例涵盖算术与位运算简化、MBA 恒等式、magic-number 除法识别、
wrapping 算术可靠性回归，以及解析器/转换器。

## 限制

- 仅支持整数算术（无浮点数）。
- 表达式大小受可用内存限制。
- 非常复杂的表达式可能在迭代/重启限制内无法收敛。

## 许可证

本项目根据 MIT 许可证条款授权。

## 致谢

- 使用 [egglog-experimental](https://github.com/egraphs-good/egglog-experimental) 构建
- 使用 [clap](https://github.com/clap-rs/clap) 进行命令行参数解析
- MBA 恒等式取自《Hacker's Delight》及等式饱和 MBA 研究

---

**注意**：此工具主要用于教育和研究目的，展示如何将等式饱和应用于代数简化与
MBA 反混淆。
