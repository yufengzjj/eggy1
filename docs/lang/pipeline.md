# 组、元素和管线

## 1. 数据模型

### 1.1 组和元素

- **组**（`group`）是一个有序集合，元素是**项**（`term`）及其附带的信息；同一个组的元素彼此等价，第一个元素在最前。每一步拿到一个值，给出另一个值（《[求值](evaluation.md)》 第 2 节）。
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

**管线**是一串步骤（`a | b | c`），`|` 和 `|` 之间可以是任何表达式。输入怎样填入、值怎样在步骤之间传、组和元素怎样相接，见《[求值](evaluation.md)》 第 1 至 3 节。

赋值（`x = e`）对当前的输入求 `e`，在**这一步之后的部分**里绑定 `x`，输入原样传下去（《[求值](evaluation.md)》 第 2 节）；`e` 可以是表达式（`x` 存数），也可以是给出组的步骤（`x` 是组变量，《[变量与作用域](variables.md)》 第 5 节）。宏解析时展开成步骤（`on`、`off` 的名字只能是开关：内部 pass 和《[化简库的变量](../lang-lib/variables.md)》 第 1 节的其他开关）。语义：

```
f | rest        ≡  先 f，再 rest                  （复合）
x = e | rest    ≡  在 x = e 之下运行 rest          （绑定）
```

同 Haskell 的 do 块：`do { f; let x = e; rest }` 里的 `let` 不是函数，作用到块尾。由此得出：序列是作用域（《[变量与作用域](variables.md)》 第 1 节）；赋值作最后一步什么也影响不到（《[检查与警告](errors.md)》的警告）；`on`、`off` 只能是宏。

检查时每一步给出的是这几种之一：组、一个项（`main`、`(index i r)` 之后，在一个项上逐个元素的 pass 之后，以及原样传下输入的 `save`、`label`、`clear`、`note`、`id`、`filter`、`within`、`settle`、`pre_done`、`print`、`assert` 和赋值之后）、数、文本、元组。函数类型的参数拿到什么输入见《[求值](evaluation.md)》 第 5 节。`def` 的函数体按它的输入检查：输入是项时是一个项，否则是组。没写类型的参数用同一条规则推出类型（《[函数定义](functions.md)》 第 2 节）：一个类型还不知道的值流进一步时，取那一步要的输入类型。
