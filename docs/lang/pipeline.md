# 组、元素和管线

## 1. 数据模型

### 1.1 组和元素

- **组**（`group`）是一个有序集合，元素是**项**（`term`）及其附带的信息；同一个组的元素彼此等价，第一个元素在最前。每一步拿到一个组，给出另一个组（或一个数、一段文本，第 2 节），所以给出组的步骤能接在任何步骤后面。
- **大小**是项的树节点数：每个变量、常数、运算各算 1，共享的子项按出现次数重复计算。
- **相同**指两个项结构完全相同：不按交换律、结合律归一，常数按值比较。`union`、`best` 去重，`fix` 判断"不再变化"，`same` 判断"同一个项"，用的都是这个标准。
- 组可以是空的。空组照常往下传，各步骤遇到空组时怎么办，见《[表达式](expressions.md)》，《[化简库的内置函数](../lang-lib/builtins.md)》 第 3 节。

### 1.2 附带信息

| 信息 | 含义 | 谁会改它 |
|---|---|---|
| **来源**（origin） | 产生它的 pass、`cand` 名等；`--stats` 按它计数，函数 `abstracted` 读它 | alternative、`origin`（`cand`）、`tag`、`smaller`、`pre_done`、`prepass`、`egglog` |
| `used` | 产生它的 pass 里，`wide_blocks`/`clustered` 是否给过被保留的形式；函数 `used_wide`、`used_clustered` 读它 | 单项 pass 和 `regions` 并入新的位 |
| `rewrites` | 产生它用了多少次未缓存的 `rewrite`；函数 `few_rewrites` 读它 | 单项 pass 累加 |

规则：
- 单项 pass 的结果继承输入元素的信息，再并入这次的 `used` 和 `rewrites`。
- 整组的 pass 给出的项如果和某个输入元素相同，就用那个输入元素（连同它的信息）。

来源会影响结果：`abstracted` 读它，`first` 比较"与输入不同"时也比较来源。

## 2. 管线

**管线**是一串步骤（`a | b | c`），`|` 和 `|` 之间可以是任何表达式。每个函数的最后一个参数是它的输入：调用少写这个参数时，由这一步的输入填入（`a | (f x)` 即 `(f x a)`，`a | f` 即 `(f a)`）。一步是否**用到输入**、给不给出值，解析时就定下：

- **用到输入**：一步里某处有一个少写了最后一个参数的调用（最外层的，或嵌在参数里的、括号里的步骤），或数值参数里读输入的函数（`(print "size" (size main))`）。
- **给出值且用到输入**：它的值往下传，作为下一步的输入。怎么接只看下一步要的输入类型（下面的组和元素），接不上就报错：给出数或文本的一步后面再接一步报 `size gives num; rewrite takes t:term`（`show gives text; ...` 同理）。管线最后一步的值是整条管线的值：`(a | main | size)` 给出一个数（《[表达式](expressions.md)》 第 3 节）；以数结束的管线写在要组的地方报 `rewrite | size gives a number, not a group`。
- **不给出值**：没有返回值的函数（`print`、`assert`）和赋值照常执行，输入原样传给再下一步。
- **给出值但没用到输入**（写在 `|` 后面的组变量 `t`、写全参数的调用 `(twice rewrite t)`、`(parse "x")`、不读输入的表达式）：照常执行，值被丢掉，输入往下传，给警告 `t does not take the input; its value is dropped — write (t | ...) to start from it`。
- **从别的组开始**：管线开头的值从它开始（`t | unify_operands | ...`；每条顶层语句、每个管线参数都是一条管线的开头）；括号里以值开头的管线不看输入，从那个值开始，它的值照常往下传（`a | (t | b) | c`、`(seq t)`、`((parse "a"))`、`(origin n (t | ...))`）。

赋值（`x = e`）对当前的输入求 `e`，在**这一步之后的部分**里绑定 `x`，输入原样传下去；`e` 可以是表达式（`x` 存数），也可以是给出组的步骤（`x` 是组变量，《[变量与作用域](variables.md)》 第 5 节）。宏解析时展开成步骤（`on`、`off` 的名字只能是开关：内部 pass 和《[化简库的变量](../lang-lib/variables.md)》 第 1 节的其他开关）。语义：

```
f | rest        ≡  先 f，再 rest                  （复合）
x = e | rest    ≡  在 x = e 之下运行 rest          （绑定）
```

同 Haskell 的 do 块：`do { f; let x = e; rest }` 里的 `let` 不是函数，作用到块尾。由此得出：序列是作用域（《[变量与作用域](variables.md)》 第 1 节）；赋值作最后一步什么也影响不到（《[检查与警告](errors.md)》的警告）；`on`、`off` 只能是宏。

**组和元素**（一条规则，解析时由 `src/lang/flow.rs` 检查，运行时没有额外的开销）：一个组送进输入是 `term` 的函数时，对组里每个元素各调用一次，结果按原来的顺序收集（第一个元素的结果在前），去掉重复的：

| 函数的返回 | 结果 |
|---|---|
| `term` | 收集成组；结果不变时保留原元素（单项 pass、polish） |
| `term?` | 给出 none 的不收（alternative） |
| `group` | 各个结果组按顺序接起来，去掉重复的（`prepass`、`reprint`） |
| 数、文本 | 报错，要写明对哪个元素：`size takes t:term? and gives num; its input here is a group: write the element, as in (size main) or (size (index i r))` |

没有隐式的"取第一个元素"：条件里写 `(if ((size main) < 3) ...)`，不写 `(if (size < 3) ...)`。逐个元素的条件是 `term->num` 的函数参数（`(filter (size < 3))`、`(any C)`、`(all C)`），由函数对每个元素调用，不受这条影响。反过来，一个项送进输入是 `group` 的函数时是只含它的组，`term?` 的 none 是空组；`term?` 也可以给要 `term` 的地方（none 时不调用，数值函数得 0）。

检查时每一步给出的是四种之一：组、一个项（`main`、`(index i r)` 之后，在一个项上逐个元素的 pass 之后，以及原样传下输入的 `save`、`label`、`clear`、`note`、`id`、`filter`、`within`、`settle`、`pre_done`、`print`、`assert` 和赋值之后）、数、文本。类型是 `group->num` 或 `pipe` 的函数参数拿到这一步的输入（所以 `main | (if mixed ...)` 里的 `mixed` 用在一个项上），`term->num` 的参数拿到一个项。`def` 的函数体按它的输入检查：输入是项时是一个项，否则是组。没写类型的参数用同一条规则推出类型（《[函数定义](functions.md)》 第 2 节）：一个类型还不知道的值流进一步时，取那一步要的输入类型。
