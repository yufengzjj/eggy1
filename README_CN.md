# eggy1

一个基于 egglog 重写的 Rust 命令行工具，用于简化中缀算术表达式。

## 功能特性

- **表达式简化**：使用代数规则简化算术表达式
- **多数字类型支持**：支持不同的数字类型（默认：i64）
- **完整的运算符支持**：处理算术运算（`+`, `-`, `*`, `/`, `%`）、位运算（`&`, `|`, `^`, `~`, `<<`, `>>`）和括号
- **灵活的输出格式**：可以输出简化后的表达式、egglog 规则格式或编译后的表达式格式
- **可自定义的迭代限制**：通过可配置的迭代限制控制简化深度

## 安装

### 从源码安装

```bash
# 克隆仓库
git clone <repository-url>
cd eggy1

# 构建并安装
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
Usage: eggy1.exe [OPTIONS] <EXPR>

Arguments:
  <EXPR>  要简化的中缀表达式

Options:
  -r, --rule-compile             输出表达式的 egglog 规则格式而不是简化
  -e, --expr-compile             输出表达式的 egglog 格式而不是简化
  -n, --num-type <NUM_TYPE>      使用的数字类型 [默认值: i64] [可能的取值: i64, u64, i32, u32, i16, u16, i8, u8]
  -i, --iter-limit <ITER_LIMIT>  最大简化迭代次数 [默认值: 30]
  -h, --help                     打印帮助信息
  -V, --version                  打印版本信息
```

### 示例

#### 简化示例

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

# 复杂表达式
eggy1 "((a + b) * (a - b)) - (a * a - b * b)"
# 输出: 0
```

#### 规则编译模式

从表达式生成 egglog 规则：

```bash
eggy1 -r "x * (y + z)"
# 输出: (Mul x (Add y z))
```

#### 表达式编译模式

从表达式生成egglog的表达式：

```bash
eggy1 -e "a + b * c"
# 输出: (Add (Var "a") (Mul (Var "b") (Var "c")))
```

#### 调整迭代限制

控制简化深度：

```bash
eggy1 -i 100 "very_complex_expression"
```

## 工作原理

该工具使用 [egglog-experimental](https://github.com/egraphs-good/egglog-experimental) 进行等式饱和和项重写。简化过程包括：

1. **解析**：将中缀表达式转换为抽象语法树
2. **规则应用**：使用 egglog 应用代数简化规则
3. **提取**：从 e-graph 中提取最简单的等价表达式

### 支持的简化规则

- 常量折叠（例如：`1 + 2 → 3`）
- 恒等元和零元消除（例如：`x + 0 → x`, `x * 1 → x`）
- 代数规范化
- 位运算简化
- 算术简化

## 开发

### 项目结构

```
src/
├── main.rs          # CLI 界面和主要简化逻辑
├── expr_convert.rs  # 表达式解析和转换工具
Cargo.toml          # 项目配置和依赖
```

### 从源码构建

```bash
# 构建项目
cargo build --release

# 运行测试
cargo test

# 使用调试输出运行
cargo run -- "1 + 2"
```

### 添加新规则

简化规则在 `main.rs` 的 `make_egg` 函数中定义。要添加新规则：

1. 将规则添加到 `make_egg` 中的相应规则集
2. 确保规则保持等价性
3. 使用各种表达式测试以验证正确性

## 测试

项目包含表达式简化的全面测试：

```bash
# 运行所有测试
cargo test

# 运行特定测试模块
cargo test expr_convert
cargo test simplify
```

测试用例涵盖：
- 基础算术运算
- 位运算
- 变量处理
- 边界情况和错误条件

## 性能考虑

- 默认迭代限制（30）平衡了彻底性和性能
- 包含许多变量的复杂表达式可能需要更高的迭代限制
- 工具使用 egglog 高效的 e-graph 数据结构进行规则应用

## 限制

- 目前仅支持整数算术（无浮点数）
- 表达式大小受可用内存限制
- 非常复杂的表达式可能在迭代限制内无法收敛

## 贡献

欢迎贡献！请随时为以下内容提交拉取请求：
- 新的简化规则
- 性能改进
- 额外的表达式类型
- 错误修复
- 文档改进

## 许可证

本项目根据 MIT 许可证条款授权。

## 致谢

- 使用 [egglog-experimental](https://github.com/egraphs-good/egglog-experimental) 构建
- 使用 [clap](https://github.com/clap-rs/clap) 进行命令行参数解析
- 灵感来源于代数简化和项重写研究

## 支持

对于问题、疑问或功能请求，请：
1. 检查现有测试用例中的类似功能
2. 查看命令行帮助（`eggy1 --help`）
3. 在项目仓库中创建问题

---

**注意**：此工具主要用于教育和演示目的，展示如何在实践中使用 egglog 进行代数简化。