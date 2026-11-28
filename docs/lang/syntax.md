# 词法和语法

## 1. 词法

- 空白只用来分隔；`#` 到行尾是注释。
- **名字**以字母或 `_` 开头，只含字母、数字和 `_`：`polish_factor`、`semi_bit_split`、`split_runs`。`-`、`/` 这些有含义的符号都不在名字里，所以 `size-mul` 是 `size - mul`，`x/2` 是 `x / 2`。旧的带 `/` 的名字连写时报错并给出新名字：`polish/factor` 报 `names cannot contain '/': write polish_factor`（`/` 换成 `_` 后是已知名字时），`save/t`、`off/relate`、`egglog/x` 报 `write save/t as (save t)` 这样的提示；其余的 `a/b` 是除法。
- **数**是十进制非负整数，最大 18446744073709551614（2^64 - 2；再大报 `number too large`）。
- **字符串**写在双引号里：`"max_leaves is at most 6"`。只认两种转义：`\"` 是引号，`\\` 是反斜杠；别的 `\` 报 `unknown escape`。字符串不跨行（行尾还没收尾报 `unclosed string`），里面的 `#`、括号、空白和 `;` 都是字符串的一部分。打印时照读入时的写法写回。用作参数（`assert` 的消息、`print` 的值）、`parse` 的输入，或单独一条顶层语句（它的值是这段文本）。
- 内置的值只有 `none`（《[变量与作用域](variables.md)》 第 2 节）。`on`、`off` 是宏名（《[变量与作用域](variables.md)》 第 4 节），不是值。
- 其他记号：`( ) | = || && ! + - * / < <= > >= == != @ : ,`。`=` 是赋值，`==` 是比较；`@` 写 `def` 的属性，`:` 写参数的类型（《[函数定义](functions.md)》 第 1、2 节），`,` 隔开元组的位置（《[元组](tuples.md)》）。

## 2. 语法

```
source  := item*                           # 程序（《[管线语言](README.md)》 第 1 节），每项到行尾为止（在括号里或行尾是 | 时接着读下一行）
item    := def | NAME '=' VALUE | '(' 'import' STRING ')' | statement
statement := program | numpipe | expr | STRING | program '|' text | text
text    := 'show' | '(' 'show' input ')'   # 给出文本的函数，只作顶层语句的最后一步
program := step ('|' step)*                # 一条序列（seq）
numpipe := step ('|' step)* '|' expr       # 最后一步给出一个数（《[表达式](expressions.md)》 第 3 节）
step    := NAME                            # 不带参数的函数（包括 def 定义的）、let 名，或组值（《[函数定义](functions.md)》 第 3 节）
         | expr                            # 用到输入的给出数，接下一步时按它的输入类型（《[组、元素和管线](pipeline.md)》 第 2 节）
         | NAME '=' expr                   # 赋值（《[变量与作用域](variables.md)》）：右边是数，NAME 是存数的变量
         | NAME '=' step                   # 绑定组变量（《[变量与作用域](variables.md)》 第 5 节）：右边给出组
         | NAME ':' TYPE '=' (expr | step) # 绑定函数变量（《[函数定义](functions.md)》 第 8 节）
         | '(' FUNC arg* input? ')'        # 函数调用（《[化简库的内置函数](../lang-lib/builtins.md)》 第 3 节、《[函数定义](functions.md)》 第 3 节），或宏 on/off
         | '(' program ')'                 # 分组：一条嵌套的序列
input   := GROUP | '(' program ')'         # 显式写出的输入（《[函数定义](functions.md)》 第 3 节）
expr    := expr '||' expr | expr '&&' expr | '!' expr
         | sum CMP sum | sum
sum     := sum ('+' | '-') sum | sum ('*' | '/') sum | atom
atom    := NUM | 'none'
         | NAME                            # 变量，或不带参数、返回数的函数
         | '(' NUMFUNC arg* input? ')'     # 数值函数的调用：(size (main R))、(same (main R))、(any C)、(minimal g)、(big 3)（《[表达式](expressions.md)》 第 3 节）
         | '(' expr ')'
         | '(' numpipe ')'                 # 括号里在最外层有 | 时
earg    := atom | '!' earg                 # 带参数的函数里的表达式参数
CMP     := '<' | '<=' | '>' | '>=' | '==' | '!='
def     := '(' 'def' ATTR* '(' NAME param* ')' body ')'     # 定义函数（《[函数定义](functions.md)》），是 --passes 的一项
         | '(' 'let' NAME program ')'
ATTR    := '@inline' | '@timed'
param   := NAME | NAME ':' TYPE            # TYPE 是 pipe、group、num、name，或函数类型 A->B（《[函数定义](functions.md)》 第 8 节）
body    := program | numpipe | expr
```

- 优先级从低到高：`|`；表达式里 `||`、`&&`、`!`、比较、`+ -`、`* /`。同级左结合；比较不能连写（`a < b < c` 报错），`!a < b` 是 `!(a < b)`。
- 带参数的函数里，表达式参数（`if`、`retry`、`filter` 的条件，`fix`、`wins`、`best` 的次数，`def` 的数值参数）是一个 `earg`：数、名字、`!` 加一个参数，或括号里的表达式。所以写 `(if ((mul main) < 1) ...)`、`(fix (restarts - 1) ...)`、`(f ((size main) / 2))`，不写 `(if (mul main) < 1 ...)`。
- 序列的每一步可以是任何 `step`：函数调用、赋值、宏、分组都能接在一起。
- 表达式只有一种：条件和数是同一种东西（《[表达式](expressions.md)》）。
- `(` 后面紧跟有参数的函数名（签名里写了参数，《[化简库的内置函数](../lang-lib/builtins.md)》 第 2 节；包括带参数的 `def`）或宏名时是调用，否则是分组。表达式里只有可选参数的数值函数没写参数时也是分组：`(size)`、`(size + 1)` 是表达式，`(size (main r))`、`(minimal t)` 是调用（后面是一个组变量、名字或 `(` 时）。内置函数名、宏名、`extern` 和 `def` 是保留字，不能用作 `let`、`def` 名；必须写参数的函数单独写出时报 `NAME needs parentheses`（只有可选参数的，如 `egglog`，也可以不带参数）；参数个数不对时按个数报，最后一个参数（输入）可以由 `|` 给出：`(lowbits x)` 报 `lowbits takes 1 argument; | gives the last: (lowbits t:term) term`，`(fix 3)` 报 `fix takes 3 arguments; | gives the last: ...`（个数写成 `N arguments`、`N or more arguments`、`N or N+1 arguments`；输入不是项或组时没有后半句）。
- 作为参数的管线如果含 `|`，要加括号：`(best 1 (a | b) c)`。只有一个管线参数、且它是最后一个参数的函数（`fix`、`wins`、`tag`、`smallest`……）例外：这个参数读到 `)` 为止，`(fix 3 a | b)` 就是 `(fix 3 (a | b))`。

### 2.1 名字

语言里的名字只有三类：

- **变量**有绑定，能赋值：存数的变量按作用域查找（《[变量与作用域](variables.md)》 第 1 节），组变量按词法查找（《[变量与作用域](variables.md)》 第 5 节）。
- **函数**没有绑定，最后一个参数是输入，按返回的东西分：
  - **数值函数**返回一个数：`mixed`、`size`、`(size (main R))`、`(any C)`（《[表达式](expressions.md)》 第 3 节）。
  - **组函数**返回一个组：不带参数的 `lowbits`、`rewrite`、`egglog`（《[化简库的内置函数](../lang-lib/builtins.md)》 第 4 节，习惯上叫 pass）；带参数的 `(save R)`、`(egglog LABEL)`，以及参数里有管线的**高阶函数** `(best K a b)`、`(fix N p)`、`(if C a b)`（《[化简库的内置函数](../lang-lib/builtins.md)》 第 3 节）。
  - **没有返回值的函数**：`print`、`assert`，作一步时原样传下输入（《[组、元素和管线](pipeline.md)》 第 2 节）。
  - 内置函数分哪一类、怎么调用、带什么参数，都由 `src/builtins.pipe` 里的签名决定（《[化简库的内置函数](../lang-lib/builtins.md)》 第 2 节）；`def` 定义的函数的签名由函数体推出（《[函数定义](functions.md)》）。
- **宏**在解析时展开：`let`、`on`、`off`、`smallest`（《[变量与作用域](variables.md)》 第 4 节）。

名字按位置解释，放错位置是类型错误，解析时报出：

| 位置 | 要的是 |
|---|---|
| 步骤 | 任何函数（包括 `def` 定义的）、`let` 名、宏、组值，或表达式（《[组、元素和管线](pipeline.md)》 第 2 节） |
| `=` 左边 | 变量（存数的，或组变量） |
| 表达式里 | 存数的变量（全局变量、局部数变量）、数值函数（包括返回数的 `def`）、数值参数、函数变量和函数参数（用在输入上） |

函数不建作用域，只有调用是一次运行的函数例外（`def` 定义的和《[化简库的内置函数](../lang-lib/builtins.md)》 第 1 节的那几个，《[函数定义](functions.md)》 第 4 节）。内置函数不绑定任何变量，所以这不影响什么；`on`、`off` 必须是宏，就是因为函数里的绑定会在返回时撤销。

名字不能重复：变量、函数、`let` 名、`def` 名互不同名（《[函数定义](functions.md)》 第 6 节）。只有一个例外：内部 pass 的函数和它的开关变量同名。`relate` 写在步骤位置时调用这个函数，写在表达式里或 `=` 左边时是它的开关变量（赋值右边见《[变量与作用域](variables.md)》 第 6 节）。
