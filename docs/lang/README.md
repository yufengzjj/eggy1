# 管线语言

eggy1 执行的是语言写的程序：调用方给出一段源文本，从上到下执行一次。化简的流程由几条管线描述，默认的写在库 `src/default.pipe` 里，程序用 `(import "default")` 读入；命令行 `eggy1` 把选项写成这样一段程序再执行它，`--passes` 的项是它的简写，`--show-passes` 打印当前的全部设置。本文是这门语言的参考：程序、名字、数据模型、语法、变量与作用域、函数定义、表达式、内置函数、`--passes` 的写法、静态检查。

- [词法和语法](syntax.md)
- [组、元素和管线](pipeline.md)
- [变量与作用域](variables.md)
- [函数定义](functions.md)
- [表达式](expressions.md)
- [检查与警告](errors.md)
- [化简库的内置函数](../lang-lib/builtins.md)
- [化简库的变量](../lang-lib/variables.md)
- [命令行和 --passes](../cli.md)

语言里的名字只有三类：**变量**（《[变量与作用域](variables.md)》，《[化简库的变量](../lang-lib/variables.md)》）、**函数**（内置的见《[化简库的内置函数](../lang-lib/builtins.md)》 第 2 节，《[表达式](expressions.md)》 第 3 节，《[化简库的内置函数](../lang-lib/builtins.md)》 第 3、4 节，用户定义的见《[函数定义](functions.md)》）、**宏**（《[变量与作用域](variables.md)》 第 4 节）。值是数、文本、函数值，或**组**：一个有序集合，它的元素是**项**（`term`），第一个元素在前。函数的最后一个参数是**输入**，调用时少写它就由这一步的输入填入（`a | (f x)` 即 `(f x a)`）；函数返回一个数、一个组、一个项或一段文本，也可以没有返回值（`print`、`assert`）。eggy1 的化简流程由几个**定义的函数**（管线）描述。

## 1. 程序

一个**程序**是一段源文本，由顶层项组成，按顺序执行一次：

- 定义：`(let NAME p)`、`(def ...)`（《[函数定义](functions.md)》）；`NAME = VALUE`：`NAME` 还不是变量、右边给出数时**定义**全局变量（《[化简库的变量](../lang-lib/variables.md)》），已经是全局变量时是对它的**赋值**。
- `(import "PATH")`：只能写在顶层，解析时处理（不是运行时的函数）。先按导入它的文件所在的目录找（调用方给的文本按当前目录），再找宿主登记的源文件（化简部分把 `src/default.pipe` 编进程序，登记为 `"default"`），都没有时报错。被导入文件的各项在导入的位置展开：定义照常登记，顶层语句在那里执行。同一个程序里一个文件只导入一次（再写不起作用），成环报错并列出环上的文件（`import cycle: a.pipe -> b.pipe -> a.pipe`）。不分命名空间，重名照现有规则报错。`src/builtins.pipe` 不经 `import`，内置函数登记时就带上了。
- **语句**：任何步骤、管线或表达式（`(parse "x + y") | simplify | main | show`、`t = (parse "x")`、`(print "hello world")`、`1 + 2`）。

顶层是**一条序列**：各项的步骤依次是它的步骤（`a | b` 写在顶层就是两步），开头**没有输入**（不是空组）；给出值的步骤（组、数或文本）把值交给下一步，赋值和没有返回值的步骤照常传下。每条语句是一条管线的开头，所以以值开头的语句（`(parse s)`、组变量）从那个值开始。顶层的赋值绑定在程序最外层的作用域里，程序结束时撤销。所以 `(print "hello world")` 直接能写（程序没有值）；要用组时先由一个值开头：`(parse s)`、组变量。在还没有值的时候写一个读输入的步骤或调用（`rewrite`、`simplify`、`t = rewrite`、单独的 `show`、`(size main)`、`(moved)`），检查时报错 `rewrite has no input here: the top level of the program starts with none; write its input, as in (rewrite t), or start from a value, as in t | rewrite; ...`。

程序的**结果**是最后一条顶层语句的值：数、组、文本或函数值（最后一步给出组时是那时的组）；最后一项是定义或赋值时没有值（赋值不给出值，以免和 `x = e` 读右边的规则混淆）。

**执行函数**（Rust，`lang::run`）：`run(source, globals)` 解析、检查、执行，返回结果和警告（`Outcome { value, warnings }`），错误是一段文字（解析和检查的错误、运行时的错误都是）。`globals` 是第一步之前执行的 `NAME = VALUE`；`default.pipe` 把这类变量定义成 `none`（不产生赋值），所以调用方预先给的值留着。`Program` 可以分几次读入文本（`read`），`finish` 检查并给出警告，`execute` 执行读好的程序。

**`default.pipe` 是库**：只有定义（全局变量和它们的默认值、`let`、`def`），没有要执行的语句。它定义的 `(def (simplify g:group) g | check_limits | pipeline | (if !(any 1) g) | settle)` 是一次化简：先 `check_limits`，再 `pipeline`，`pipeline` 给出空组时用输入，最后 `settle` 记下统计。

**序言**：每个程序先读入语言自带的 `src/lang/prelude.pipe`（`Program::new`，`source::prelude()`），它只定义 `(def @inline (main g) (index 0 g))`（《[表达式](expressions.md)》 第 3 节）。

**命令行**写出的程序（`--show-passes` 第一行的注释照这个样子写在一行里，项之间用 `; `）：

```
(import "default")
num_type = u32          # -n
restarts = 2            # -m
iter_limit = 10         # -i
trace = 1               # 只在 --trace 时
<--passes 的各项写成的源文本>（《[命令行和 --passes](../cli.md)》）
(parse "EXPR") | simplify | time_limit = none | (if was_cut (print "time limit reached: ...")) | main | show
```

`eggy1` 打印程序给出的文本。bench 的子进程、测试写同样的程序（没有截断提示那两步）；`fuzz --prepass` 写 `(parse "EXPR") | (prepass prepass_steps)`。

`--show-passes` 先打印一行注释 `# The program: <上面的程序，EXPR 照写>`，再打印 `--passes` 写法的全部设置（从 `--passes` 的项开始），所以它的输出可以原样传给 `--passes`。`--show-builtins` 按调用方式列出全部内置函数的签名和说明（《[化简库的内置函数](../lang-lib/builtins.md)》 第 2 节），最后列出 `def` 的签名：`default.pipe` 的（`cand`、`simplify`）一组，`--passes` 里有 `def` 时再一组。

### 1.1 解析和打印

- `(parse s)`：`s` 是文本（字符串字面量，或 `(show ...)`），一个中缀表达式（命令行读的写法）或一个 egglog 项（`(Add (Var "x") (Num 1))`），按 `num_type` 读成只含它的组，来源 `input`。不看输入，所以是一个值（写在 `|` 后面时它的值被丢掉，《[组、元素和管线](pipeline.md)》 第 2 节）；不带 `@timed`，过了截止时刻照样读入。
- `(show t)`：一个项的中缀，常数照 `num_type` 的打印方式（和 eggy1 的输出一样）；`t` 为 none 时是空文本。输入是一个项，所以在组上写 `main | show` 或 `(show (main t))`（《[组、元素和管线](pipeline.md)》 第 2 节的组和元素）。给出文本的步骤只能是顶层语句的最后一步，或者 `parse` 的输入。
- **`num_type`** 是全局变量，值是类型名 `i64 u64 i32 u32 i16 u16 i8 u8` 之一（`num_type = u32`，右边只收类型名和 `none`），`none` 读作 `i64`。`parse`、`show`、`print`、`egglog`、`reprint`、最小性证明和各 pass 都按它（顶层每一步按当时的值定位宽）；egglog 程序按类型在第一次用到时生成。
