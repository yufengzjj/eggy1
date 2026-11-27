# 管线语言参考

eggy1 的化简流程由几条管线描述，默认的写在 `src/default.pipe` 里，`--passes` 可以替换或改写它们，`--show-passes` 打印当前的全部设置。本文是这门语言的参考：名字、数据模型、语法、变量与作用域、函数定义、表达式、内置函数、`--passes` 的写法、静态检查。

## 1. 概览

语言里的名字只有三类：**变量**（第 5、10 节）、**函数**（内置的见第 4.3、7.3、8、9 节，用户定义的见第 6 节）、**宏**（第 5.4 节）。函数的最后一个参数是**输入**（当前的候选组，写在管线里时由 `|` 填入），返回一个数或一组候选；eggy1 的化简流程由几个**定义的函数**（管线）描述。一次运行执行一个**入口程序**：

```
<default.pipe 的赋值> | <命令行的赋值> | pipeline
```

- `src/default.pipe` 定义各个函数（管线）和 `let` 名字（也可以写 `def`），并给所有变量赋默认值。
- 命令行：先是 `-m N`（`restarts = N`）、`-i N`（`iter_limit = N`），再是 `--passes` 的 `NAME=VALUE` 项、`off` 列表项，按出现顺序，都排在 `default.pipe` 的赋值之后（第 12 节）。所以 `--passes restarts=5` 盖过 `-m`。
- 从 Rust 直接进入别的管线时（测试和 `fuzz --prepass` 调用 `simplify_linear_with` 即 `prepass`、`polish`，不在任何运行里的 `rewrite`），入口换成那条管线，前面接同一段赋值（没有 `-m`、`-i` 那两步）。已经在一次运行里时，嵌套的运行不再执行它们。
- 每次 `simplify` 都从头执行入口程序，结束时撤销所有绑定，下一个表达式重新开始。

`--show-passes` 先打印一行注释 `# A run: <入口程序的各步> | pipeline`，再打印 `--passes` 写法的全部设置（只含命令行那部分赋值），所以它的输出可以原样传给 `--passes`。`--show-builtins` 按调用方式列出全部内置函数的签名和说明（第 4.3 节），`--passes` 里有 `def` 时最后单列它们的签名。

### 1.1 Rust 代码调用的函数

下面几个函数由 Rust 代码调用，函数体是管线，写在 `default.pipe` 里。`(def (NAME) P)` 可以替换它们的函数体（第 6 节），`prepass=P` 这样的项是它的简写。它们各有固定的调用方式：

| 函数 | 调用方式 | 谁调用 | 说明 |
|---|---|---|---|
| `pipeline` | 整组 | 入口程序 | 整个化简：预处理、egglog 各轮、polish、从打印结果再跑一遍 |
| `prepass` | 对主候选调用，结果替换整组 | 步骤 `prepass`；函数 `opaque`、`rebuilds`；Rust 的 `simplify_linear_with` | 预处理：造出几个重建候选，按大小排好 |
| `polish` | 对每个候选单独调用，变小才替换 | 步骤 `polish`；Rust 的 `pipe::polish` | 局部改写，只在变小时保留 |
| `rewrite` | 单项（第 9.2 节） | 步骤 `rewrite`；单项函数内部、`regions`、`again` | 带缓存的重建 |
| `simba` | alternative（第 9.3 节） | 步骤 `simba`；`poly_mba` 的线性余因子 | 线性区域的各种重建方法 |
| `sub/NAME` | 单项 | 只在单项函数内部，重建子项时 | 第 11 节 |

调用它们和调用 `def` 定义的函数一样是一次**运行**（第 6.4 节）；`polish` 对每个候选是一次单独的运行。

## 2. 数据模型

### 2.1 候选

- **候选**是一个项，以及附带的信息。一组候选彼此等价，第一个是**主候选**。每一步拿到一组候选，给出另一组，所以任何步骤都能接在任何步骤后面。
- **大小**是项的树节点数：每个变量、常数、运算各算 1，共享的子项按出现次数重复计算。
- **相同**指两个项结构完全相同：不按交换律、结合律归一，常数按值比较。`union`、`best` 去重，`fix` 判断"不再变化"，`same` 判断"同一个项"，用的都是这个标准。
- 一组候选可以是空的。空组照常往下传，各步骤遇到空组时怎么办，见第 7、8 节。

### 2.2 附带信息

| 信息 | 含义 | 谁会改它 |
|---|---|---|
| **来源**（origin） | 产生它的 pass、`cand` 名等；`--stats` 按它计数，函数 `abstracted` 读它 | alternative、`cand`、`tag`、`smaller`、`pre_done`、`prepass`、`egglog` |
| `used` | 产生它的 pass 里，`wide_blocks`/`clustered` 是否给过被保留的形式；函数 `used_wide`、`used_clustered` 读它 | 单项 pass 和 `regions` 并入新的位 |
| `rewrites` | 产生它用了多少次未缓存的 `rewrite`；函数 `few_rewrites` 读它 | 单项 pass 累加 |

规则：
- 单项 pass 的结果继承输入候选的信息，再并入这次的 `used` 和 `rewrites`。
- 列表 pass 给出的项如果和某个输入候选相同，就用那个输入候选（连同它的信息）。

来源会影响结果：`abstracted` 读它，`first` 比较"与输入不同"时也比较来源。

## 3. 词法

- 空白只用来分隔；`#` 到行尾是注释。
- **名字**以字母或 `_` 开头，可以含字母、数字、`_`、`/`：`polish/factor`、`semi/bit_split`、`split_runs`。`-` 不能出现在名字里，所以 `size-mul` 是 `size - mul`。`/` 两边是名字时要留空格：`x / 2`，因为 `x/2` 读成名字 `x/2`。
- **数**是十进制非负整数，最大 18446744073709551614（2^64 - 2；再大报 `number too large`）。
- 内置的值只有 `none`（第 5.2 节）。`on`、`off` 是宏名（第 5.4 节），不是值。
- 其他记号：`( ) | = || && ! + - * / < <= > >= == != @ :`。`=` 是赋值，`==` 是比较；`@` 写 `def` 的属性，`:` 写参数的类型（第 6.1、6.2 节）。

## 4. 语法

```
program := step ('|' step)*                # 一条序列（seq）
numpipe := step ('|' step)* '|' expr       # 最后一步给出一个数（第 7.3 节）：expr 以数值函数或返回数的函数开头
step    := NAME                            # 不带参数的函数（包括 def 定义的）、let 名，或组值（第 6.3 节）
         | NAME '=' expr                   # 赋值（第 5 节）：右边是数，NAME 是存数的变量
         | NAME '=' step                   # 绑定组变量（第 5.5 节）：右边给出候选
         | '(' FUNC arg* input? ')'        # 函数调用（第 8 节、第 6.3 节），或宏 on/off
         | '(' program ')'                 # 分组：一条嵌套的序列
input   := GROUP | '(' program ')'         # 显式写出的输入（第 6.3 节）
expr    := expr '||' expr | expr '&&' expr | '!' expr
         | sum CMP sum | sum
sum     := sum ('+' | '-') sum | sum ('*' | '/') sum | atom
atom    := NUM | 'none'
         | NAME                            # 变量，或不带参数、返回数的函数
         | '(' NUMFUNC arg* input? ')'     # 数值函数的调用：(size R)、(same R)、(any C)、(mixed t)、(big 3)（第 7.3 节）
         | '(' expr ')'
         | '(' numpipe ')'                 # 括号里在最外层有 | 时
earg    := atom | '!' earg                 # 带参数的函数里的表达式参数
CMP     := '<' | '<=' | '>' | '>=' | '==' | '!='
def     := '(' 'def' ATTR* '(' NAME param* ')' body ')'     # 定义函数（第 6 节），是 --passes 的一项
         | '(' 'let' NAME program ')'
ATTR    := '@inline' | '@pipe'
param   := NAME | NAME ':' TYPE            # TYPE 是 pipe、group、num、name
body    := program | numpipe | expr
```

- 优先级从低到高：`|`；表达式里 `||`、`&&`、`!`、比较、`+ -`、`* /`。同级左结合；比较不能连写（`a < b < c` 报错），`!a < b` 是 `!(a < b)`。
- 带参数的函数里，表达式参数（`if`、`retry`、`filter` 的条件，`fix`、`wins`、`best` 的次数，`def` 的数值参数）是一个 `earg`：数、名字、`!` 加一个参数，或括号里的表达式。所以写 `(if (mul < 1) ...)`、`(fix (restarts - 1) ...)`、`(f (size / 2))`，不写 `(if mul < 1 ...)`。
- 序列的每一步可以是任何 `step`：函数调用、赋值、宏、分组都能接在一起。
- 表达式只有一种：条件和数是同一种东西（第 7 节）。
- `(` 后面紧跟有参数的函数名（签名里写了参数，第 4.3 节；包括带参数的 `def`）或宏名时是调用，否则是分组。表达式里只有可选参数的数值函数没写参数时也是分组：`(size)`、`(size + 1)` 是表达式，`(size r)`、`(size (rewrite))`、`(mixed t)` 是调用（后面是一个组变量或 `(` 时）。内置函数名、宏名、`extern` 和 `def` 是保留字，不能用作 `let`、`def` 名；必须写参数的函数单独写出时报 `NAME needs parentheses`（只有可选参数的，如 `egglog`，也可以不带参数）；没有参数的函数后面跟了参数（`(lowbits x)`）报 `NAME takes no arguments`。
- 作为参数的管线如果含 `|`，要加括号：`(best 1 (a | b) c)`。只有一个管线参数、且它是最后一个参数的函数（`fix`、`wins`、`tag`、`smallest`……）例外：这个参数读到 `)` 为止，`(fix 3 a | b)` 就是 `(fix 3 (a | b))`。

### 4.1 名字

语言里的名字只有三类：

- **变量**有绑定，能赋值：存数的变量按作用域查找（第 5.1 节），组变量按词法查找（第 5.5 节）。
- **函数**没有绑定，最后一个参数是输入，按返回的东西分：
  - **数值函数**返回一个数：`mixed`、`size`、`(size R)`、`(any C)`（第 7.3 节）。
  - **候选组函数**返回一组候选：不带参数的 `lowbits`、`rewrite`、`egglog`（第 9 节，习惯上叫 pass）；带参数的 `(save R)`、`(egglog LABEL)`，以及参数里有管线的**高阶函数** `(best K a b)`、`(fix N p)`、`(if C a b)`（第 8 节）。
  - 内置函数分哪一类、怎么调用、带什么参数，都由 `src/builtins.pipe` 里的签名决定（第 4.3 节）；`def` 定义的函数的签名由函数体推出（第 6 节）。
- **宏**在解析时展开：`let`、`on`、`off`、`smallest`（第 5.4 节）。

名字按位置解释，放错位置是类型错误，解析时报出：

| 位置 | 要的是 |
|---|---|
| 步骤 | 候选组函数（包括 `def` 定义的）、`let` 名、宏，或组值 |
| `=` 左边 | 变量（存数的，或组变量） |
| 表达式里 | 存数的变量、数值函数（包括返回数的 `def`）、数值参数 |

函数不建作用域，只有调用是一次运行的函数例外（`def` 定义的和第 1.1 节的那几个，第 6.4 节）。内置函数不绑定任何变量，所以这不影响什么；`on`、`off` 必须是宏，就是因为函数里的绑定会在返回时撤销。

名字不能重复：变量、函数、`let` 名、`def` 名互不同名（第 6.6 节）。只有一个例外：内部 pass 的函数和它的开关变量同名。`relate` 写在步骤位置时调用这个函数，写在表达式里或 `=` 左边时是它的开关变量（赋值右边见第 5.6 节）。

### 4.2 管线

**管线**是一串步骤（`a | b | c`）。不以值开头的管线是一个 `group → group` 的函数值（输入是隐含的），签名里的 `pipe` 类型就是它；以值开头的管线（`g | a | b`）是那个值依次经过各步的结果（第 6.3 节）。每一步是两种之一：

- **函数**：把当前候选组交给它，结果交给下一步。
- **赋值**（`x = e`）：对当前候选组求 `e`，在**这一步之后的部分**里绑定 `x`，候选组原样传下去。`e` 可以是表达式（`x` 存数），也可以是给出一组候选的步骤（`x` 是组变量，第 5.5 节）。

宏解析时展开成这两种步骤（`on`、`off` 的名字只能是开关：内部 pass 和第 10.1 节的其他开关）；表达式只出现在赋值右边、函数参数、函数体和以数结束的管线的最后一步。语义：

```
f | rest        ≡  先 f，再 rest                  （复合）
x = e | rest    ≡  在 x = e 之下运行 rest          （绑定）
```

同 Haskell 的 do 块：`do { f; let x = e; rest }` 里的 `let` 不是函数，作用到块尾。由此得出：序列是作用域（第 5.1 节）；赋值作最后一步什么也影响不到（第 13 节的警告）；`on`、`off` 只能是宏。

**相邻步骤的类型**：左边给出候选组，右边要候选组。给出数的步骤（数值函数、返回数的函数）只能作管线的最后一步，这条管线就给出数（第 7.3 节）；写在 `|` 前面报 `size gives a number; rewrite takes candidates`，以数结束的管线写在要候选的地方报 `rewrite | size gives a number, not candidates`。组值写在 `|` 后面（`a | t`）丢掉前面的结果，给警告 `t drops its input`（`(load t)` 也这样，但常用，不警告）。

### 4.3 内置函数的签名

内置函数的签名声明在 `src/builtins.pipe` 里（在 `default.pipe` 之前读入），函数体在 Rust 里实现；第 7.3、8、9 节的表是它们的说明，完整的签名以 `builtins.pipe` 为准：

```
(extern [@ATTR ...] (NAME PARAM:TYPE ... INPUT:TYPE) RESULT)
```

- 类型：`num`（一个数）、`term`（一个候选）、`term?`（一个候选或没有，只作返回类型）、`group`（一组候选）、`name`（统计名、来源名或记录寄存器名），以及函数类型 `A->B`（`A->B->C` 是 `A->(B->C)`）。`pipe` 是 `group->group` 的简写：管线，原样传进去，在函数里运行；两种写法相同，打印成 `pipe`。`group` 写在参数里（不是最后一个）时是一个组变量，调用时写它的名字（`(load r:group g:group) group`）。`TYPE...` 是一个或多个，`TYPE?` 可以省略（只用于 `pipe`、`group`、`name`）。
- 作参数时，`num` 是调用时对输入求一次值的表达式（`best` 的个数、`fix` 和 `wins` 的次数）；`term->num` 是对每个候选单独求值的条件（`filter`、`any`、`all`）；`group->num` 是对一组候选求值的条件（`if` 对输入，`retry` 对 `a` 的结果）。这两种函数类型的参数也写成表达式，就是以隐式输入为参数的函数（第 6.3 节的隐式输入），所以写法和 `num` 参数一样。内置函数的参数只用 `pipe`、`term->num`、`group->num` 这几种函数类型，其他函数类型的参数还不支持。
- 最后一个参数是**输入**（`term` 或 `group`），写在管线里时由 `|` 填入，不写；也可以显式写出（第 6.3 节）。返回类型写在最后。
- 声明前紧挨着的一行注释是它的说明。
- 属性：`@pipe`：输入可以由 `|` 填入，所以能写成步骤（`a | (f x)` 即 `(f x a)`）；内置函数都带它。`@bookkeeping`：只搬动候选，过了时限照常执行（第 5.3 节）；`@simplify_only`：只能出现在 `pipeline` 里（`egglog`、`reprint`），因为只有 `simplify` 的运行才有 e-graph；`@uncounted`：过了时限照样跳过，但这次跳过不把运行记为截断，也不计入 `time_limit/skipped`（`note`），不能和 `@bookkeeping` 一起写。
- `extern` 只能写在 `builtins.pipe` 里，写在 `--passes` 或管线里报错。宏 `let`、`on`、`off` 和赋值不是函数，没有声明（宏 `smallest` 有声明，参数照它读）；第 1.1 节的 `pipeline`、`sub/NAME` 不能在步骤里调用，也没有声明。

调用方式由输入和返回类型决定，第 9 节的四种由此得出：

| 输入 → 返回 | 调用方式 |
|---|---|
| `group → group` | 整组 |
| `term → term` | 对每个候选调用；结果不变时保留原候选（单项、polish、`polish`） |
| `term → term?` | 对每个候选调用；没有结果时去掉这个候选（alternative） |
| `term → group` | 对主候选调用，结果替换整组（`prepass`、`reprint`） |
| `term → num` | 对主候选求值；组为空时得 0 |
| `group → num` | 对整组求值；组为空时得 0（`any`、`all`、`minimal`、`used_wide`、`used_clustered`，以及不看候选的 `moved`、`cofactor`） |

例外：`(size R)` 读组变量 `R` 的主候选，不看输入，所以输入为空时也不得 0。

解析照签名读参数：`num`、`term->num`、`group->num` 参数是一个 `earg`（数值函数 `any`、`all` 的参数是整个表达式），`group`、`name` 参数是一个名字，`pipe...` 是一个或多个步骤，第 4 节末尾说的那种 `pipe` 参数读到 `)` 为止，其他 `pipe` 参数各是一个步骤。位置、参数个数和种类的检查都照签名做（第 13 节），报错时附上签名。

## 5. 变量与作用域

### 5.1 一条规则

> `NAME = VALUE` 在**当前作用域**里绑定变量 `NAME`；同一作用域里再赋值，就是覆盖这个绑定。读 `NAME` 时先在当前作用域找，没有就沿**调用链**往上找，直到入口程序。作用域结束时，它的绑定随之消失。

- 这条规则说的是存数的变量；存候选组的组变量按词法查找，每次运行一套（第 5.5 节）。
- **作用域**有三种：序列（`a | b | ...`，包括分组 `( ... )` 和 `(seq ...)`）、`scope`、每条管线的一次运行。其他形式（`if`、`fix`、`union`、`best`……）不是作用域：`(if C x = 1)` 的绑定落在 `if` 所在的序列里，`(if C (x = 1 | p))` 的绑定只在那条分组序列里。
- "往上"沿调用链走（动态作用域）：`semi_leaves = 2 | polish` 里，`polish` 读到 2，除非它自己在内层再赋值。
- 赋值原样传下候选，所以可以写在序列的任何位置。
- 赋值右边在执行到这一步时求值，读的是当时的候选组。

普通变量是**最内层的绑定起作用**。预算和时限是**链上所有绑定都起作用**：

- **预算**（`rewrites`、`bit_split_budget`）：每用掉一次，链上每一层的绑定都减 1，任何一层到 0 就停。所以退出时外层已经减去了里面用掉的次数，里面赋得再大也超不过外层剩下的。
- **时限**（`time_limit`）：赋值时从此刻起计时，得到一个截止时刻。链上最早的截止时刻起作用，所以里层不能晚于外层。

### 5.2 值

- 变量的值是非负整数，或 `none`。每个变量开始时都是 `none`。
- `none` 比所有整数都大（+∞）。上限类变量（`split_runs`、预算、`time_limit`……）读到 `none` 就是不限。
- 布尔值就是数：开关写 1（开）或 0（关），非 0 都算开，比如 `relate = 0`、`cut = 1`。`none` 不是 0，所以作开关时算开：内部 pass 不赋值就是开着的。
- 有上限的变量（`max_leaves` 最多 6），赋超过上限的值时报错，`none` 也一样。右边是数字或 `none` 时解析时就报；是表达式时执行到这一步时报，这次运行停下，返回这个错误（`max_leaves = 8: max_leaves is at most 6`）。
- 开关不收字面的 `none`（解析时报错）；右边是表达式、算出 `none` 时，开关为开。

### 5.3 时限

- 过了截止时刻，干活的步骤原样返回输入，所以任何时候停下来结果都正确。只搬动候选的步骤照常执行：签名带 `@bookkeeping` 的函数（序列本身、`save`、`load`、`label`、`clear`、`take_min`、`filter`、`id`、`none`、`within`、`pre_done`），以及赋值和 `on`、`off`。所以组变量照常可用，时限所在的作用域结束后，外面的步骤接着运行。`note` 不是 `@bookkeeping`：过了截止时刻它和其他计算的步骤一样跳过，原样返回、什么也不记；它是 `@uncounted`，这次跳过不算截断，也不计入 `time_limit/skipped`；之后的计算步骤也都原样返回，所以最后一个真正的结果原样到达 `take_min`。`smallest` 本身不是 `@bookkeeping`，过了截止时刻整个跳过。
- 时限只在步骤之间检查，打断不了正在运行的单个步骤（一轮 egglog、一次大的 `poly_mba` 展开）。一轮 egglog 开始前，按上一轮用的时间估计：估计会超过截止时刻就跳过。
- 开关 `cut` 开着时，因时限跳过的步骤会把整次运行记为截断：`eggy1` 打印提示，bench 把没解出的用例记作 `cut`。默认 `pipeline` 开头写 `cut = 1`。不想算的地方写 `cut = 0`。
- 截断时得到的结果不进缓存。

```
a | time_limit = 1000 | b | time_limit = none | c    # 只限 b
a | (time_limit = 1000 | b) | c                     # 同上
a | time_limit = 1000 | b | c                       # b、c 共用 1000 ms
a | (if big time_limit = 200) | b | c               # 输入大时 b、c 共用 200 ms
```

### 5.4 宏：`let`、`on`、`off`、`smallest`

宏在解析时展开，不建新作用域：

- `(let NAME p)` 是一项定义，之后写到 `NAME` 的地方展开成 `p`；它就是 `(def @inline (NAME) p)`，平铺、组变量、重新定义的规则见第 6.1、6.4、6.6 节。
- `(off A B ...)` 展开成 `A = 0 | B = 0 | ...`，`(on A B ...)` 同理（`A = 1`）；`A`、`B` 必须是开关。它们不是函数：如果是函数，绑定会在返回时撤销。
- `(smallest p)` 展开成 `(clear s) | p' | (take_min s)`。`s` 是宏生成的记录寄存器名（`smallest#N`，每个 `smallest` 一个，用户写不出）。`p'` 是在 `p` 的文字里每个**计算的步骤**后面插一个 `(note s)`：计算的步骤是调用不带 `@bookkeeping`、也不带管线参数的函数（`note` 本身除外；单项 pass、alternative、`prepass`、`polish`、`take_minimal`、`reprint`、`egglog`）、调用 `def` 函数，以及 `def` 函数体里的管线参数（记它返回的候选）。插入也进到高阶函数的管线参数（`fix`、`best`、`if`、`retry`、`union`、`first`、`smaller`、`wins`、`regions`、`again`、`scope`、`tag`、`cand` 的各支）、组变量绑定的右边（`t = p` 的 `p`）、传给函数的管线参数（闭包，里面的 `note` 写的是外面的 `s`）、有数值参数的 `@inline` 函数体（共享调用处的 `smallest`；体里的管线参数后面不插，参数在调用处已经插过）和里层 `smallest` 的展开里；`let` 和没有数值参数的 `@inline` 函数已展开在文字里，照样插。不进 `def` 函数体和 `prepass`、`polish` 等定义的函数里面：它们只以返回值被看到。所以 `fix` 的各轮、`best` 落选的分支给出的候选都算，输入本身不算。`p` 是序列时展开是一个作用域，否则展开的各步在所在的作用域里执行，和 `p` 不写在 `smallest` 里时一样。`--show-passes` 照原样打印 `(smallest p)`。

### 5.5 组变量

**组变量**存一组候选（第 10 节的变量存数）。`R = p` 在当前候选组上运行步骤 `p`，把它给出的候选绑定到 `R`，当前候选组原样传下去（同其他赋值）；`R = U`（`U` 是组变量）把 `U` 的候选组绑定到 `R`；`(save R)` 是 `R = id` 的简写，`(load R)` 给出 `R` 的候选组，`(size R)`、`(same R)`、`(label R)` 读它的主候选。

```
t = (lowbits | unshift) | rewrite | (filter (size < (size t)))   # rewrite 的结果比 t 小才留下
(save t) | rewrite | t = (union (load t) id)                     # t 是 rewrite 前后的候选
(save t) | u = t | (load u)                                      # u 和 t 是同一组
```

- `p` 的步骤是本次运行的步骤：读写本次运行的组变量，外面的 `smallest` 在 `p` 的计算步骤后面照样插 `note`（第 5.4 节），过了截止时刻 `p` 的计算步骤照常跳过（绑定本身是赋值，照常执行，所以 `R` 得到当时的输入）。`p` 总是一个作用域，只是一步时也是：`t = (off relate)` 的 `off` 到 `p` 结束为止，不影响后面的步骤（所以这样写什么也不做，给警告）。
- 组变量**按词法**查找：每次运行（`pipeline`、`prepass`、`polish`、`def` 的调用……）有自己的一套，不受序列、`scope` 的作用域限制；被调用的 `def` 看不到调用处的组变量，管线参数读写写下它的那次运行的，`@inline` 调用和 `let` 共用调用处的（第 6.3、6.4 节）。存数的变量沿调用链动态查找（第 5.1 节），组变量不参与这种查找。
- 同一个名字不能既是存数的变量又是组变量（`(save keep)`、`keep = rewrite` 报错）；写成 `R = p` 时，`R` 也不能是函数、`let`、`def` 名或参数（`rewrite = id` 报错）。
- 读一个没绑定的组变量得空组（`size`、`same` 得 0）；静态检查要求读之前有可能先执行的绑定（第 13 节）。

`clear`、`note`、`take_min` 用的**记录寄存器**是另一套，和 `save`、`load` 的不相通：每个存至多一个候选，`(clear R)` 每次打开一个新的 `R`（同名的已经打开时也是），`note`、`take_min` 用最新打开的那个，`take_min` 把它关上。所以 `@inline` 函数在自己的管线参数里再被调用时，两层的 `smallest` 各用各的。记录寄存器和组变量一样属于一次运行，`@inline` 调用共享调用处的。

### 5.6 赋值的右边

赋值右边只读一次，读完按它给出的东西定是哪一种：

- 给出数（表达式，包括括号里以数结束的管线 `(prepass | size)`、`((lowbits | size) + 1)`）：赋值，左边必须是存数的变量（第 10 节）。表达式读到 `|`、`)` 或项尾为止：`split_runs = vars * 2 | split_bits`。
- 给出候选：绑定组变量（第 5.5 节）。右边是**一个步骤**，读到 `|` 或 `)` 为止：`t = rewrite | relate` 是 `(t = rewrite) | relate`；含 `|` 的管线要加括号，`t = (lowbits | unshift)`、`t = (relate = 0 | rewrite)`。右边单独一个不是变量、函数或定义的名字（后面是 `|`、`)` 或项尾）是组变量：`t = u` 把 `u` 的候选组绑定到 `t`，意思同 `t = (load u)`（两种写法各照原样打印）。
- 右边开头的名字两种都说得通时由左边定：`relate` 既是 pass 又是开关变量，`t = relate` 是 pass，`keep = relate` 是开关变量；没注解的参数 `r` 在 `keep = r` 里是数值参数，在 `t = r` 里按管线读（第 6.2 节）。
- 类型对不上是错误，报错写出两边：`keep = (lowbits | unshift)` 报 `keep is a variable that holds a number, so it cannot be bound to candidates: (lowbits | unshift) gives candidates`；前面绑定过的组变量赋数报 `t is a group variable, so it cannot hold a number: 1 gives a number`；左边是没见过的名字、右边是数时报 `unknown variable t`（多半是存数的变量写错了）；右边像表达式却读不下去时（`t = u + 1`，`u` 不是任何名字）也报 `unknown variable t`，后面附上右边的错误。

## 6. 函数定义

`def` 定义带参数的函数，调用起来和内置函数一样；签名由函数体推出，不用写。

### 6.1 写法

```
(def (NAME PARAM ...) BODY)                    # 调用是一次运行（第 6.4 节）
(def @inline (NAME PARAM ...) BODY)            # 不开运行，在调用处展开
(def @pipe (NAME PARAM ... g) BODY)            # 最后一个参数 g 是输入，由 | 填入
(def @inline @pipe (NAME PARAM ... g) BODY)
(let NAME P)                                   # 即 (def @inline (NAME) P)
pipeline=P、prepass=P、polish=P、rewrite=P、simba=P、sub/NAME=P   # 即 (def (NAME) P)
```

- `def`、`let` 和 `NAME=P` 一样是 `--passes` 的一项（`default.pipe` 里也可以写），不是管线里的步骤；之后的项里能用它定义的名字。属性写在 `(NAME ...)` 前，顺序随意；别的属性报 `unknown attribute`。
- `BODY` 是三种之一，它的类型就是函数的返回类型（第 6.5 节）：
  - 管线：返回一组候选。
  - 以数结束的管线（`lowbits | size`、`g | lowbits | size > 3`，第 7.3 节）：返回数。
  - 表达式（以数、`!`、存数的变量、数值函数、返回数的函数或数值参数开头）：返回数。
- **`@pipe`**：最后一个参数是输入，类型必须是 `group`（不写也是）；写在管线里时由 `|` 填入（`a | (f x)` 就是 `(f x a)`，`a | f` 就是 `(f a)`），也可以写全。函数体必须以值开头（`g | ...`）或是表达式，否则报 `the body of an @pipe function starts with a value`。
- **简写**：不带 `@pipe`、函数体是不以值开头的管线时，输入是隐含的：`(def (NAME P ...) BODY)` 就是 `(def @pipe (NAME P ... g) g | BODY)`。`default.pipe` 里的定义、`prepass=P` 这样的项、`let` 都是这种。
- 不带 `@pipe`、函数体以值开头时，最后一个参数只是普通参数，函数只能写全参数调用，调用是一个值，不能写在 `|` 后面（第 6.3 节）：`(def (twice p g) (p (p g)))` 的签名是 `(twice p:pipe g:group) group`。
- 函数体里的名字在读到定义时解析，所以函数只能调用在它之前定义的函数（`let`、`def`）；第 1.1 节的那几个函数在运行时取当前的定义。重新定义 `gates` 这样的 `let` 名，不会改变已经读好的 `prepass`。
- `--show-passes` 和 `Display` 把 `def` 写在各条管线之前，每个前一行注释是它的签名（`# (twice g:group) group`），照写下的样子打印（组参数带 `:group`，这样读回来不变）。`let` 和没有数值参数、不带 `@pipe` 的 `@inline` 函数已在使用处展开，不再写出；其他 `@inline` 函数照 `def` 打印（`(def @inline (lim n p) split_runs = n | p)`）。`--show-builtins` 在最后单列 `def` 的签名。

### 6.2 参数

参数有四种，和内置函数的参数类型一样：

| 种类 | 类型 | 推出它的用法 | 调用时 |
|---|---|---|---|
| 管线参数 | `pipe` | 写在步骤位置；当函数值调用（`(p g)`、`g \| p`） | 不求值，原样传进去，是闭包（第 6.3 节），函数体里每用一次就运行一次 |
| 数值参数 | `num` | 写在表达式里（赋值右边、`(fix N p)`、`(best K ...)`、`(if C ...)`、`filter`、`any`、`all` 的条件……） | 在调用处、对调用时的候选组求一次值（同赋值右边） |
| 组参数 | `group` | 写在组变量位置（`(load R)`、`(label R)`、`(size R)`、`(same R)`）；作函数值或函数的显式输入（`(p r)` 的 `r`） | 按值：调用处那个组变量的候选组 |
| 名字参数 | `name` | 写在名字位置（`(tag NAME p)`、`(cand NAME p)`、`(smaller NAME p)`、`(egglog LABEL)`、`(off NAME)`、`(on NAME)`） | 解析时代入 |

- 作为参数传给另一个函数时，取那个参数的类型。
- 可以写类型：`p:pipe`（也可写 `p:group->group`）、`r:group`、`n:num`、`x:name`；不写时第一次用到就定下。也能写别的函数类型（`pred:term->num`、`c:group->num`），但这种参数还不支持，报 `parameter pred:term->num: function types other than pipe are not supported yet`。同一个参数的用法互相矛盾（`parameter p is used as a pipeline and as a group variable`）、函数体里没用到（`parameter q is never used in the body`）都报错。
- `t = r`、函数体就是 `r` 这种位置管线和组都合适，没写类型的参数在那里按管线算；只在这种位置用到时给警告，提示写 `r:pipe` 或 `r:group`。要当组用，就写 `r:group`，或者先在组的位置用到它（`(load r)`）。
- 参数只在函数体里看得见（词法绑定），不参与存数变量的查找，不能赋值（`(save a)`、`a = ...`、`n = 3` 都报 `parameter a cannot be assigned`）；不能和变量、函数、宏、`let` 名、`def` 名、`none`、`def`、`let`、`extern` 或函数自己同名，也不能重复。
- 读参数的规则和内置函数一样（第 4.3 节）：数值参数是一个 `earg`（`(f size / 2)` 要写成 `(f (size / 2))`），只有一个管线参数、且它是最后一个参数时读到 `)` 为止，其他管线参数各是一个步骤，组参数和名字参数各是一个名字。个数、种类不对时报错附上签名：`f takes a group variable and a pipeline: (f r:group p:pipe g:group) group`；表达式参数处写了管线时还先给出那个表达式的错误。有参数的函数单独写出时报 `NAME needs parentheses`，没有参数的写了参数报 `f takes no arguments: (f g:group) group`。

**数值参数**是值，不是变量：函数体里读到的是调用时算出的值，函数体先改了候选也不变（`(def (f n p) p | (filter (n == 7)))` 调用成 `(f size rewrite)` 时 `n` 是调用时输入的大小）；被调用的函数看不到它（写了就是未知的名字）；对缓存没有影响（缓存只记 Rust 代码读的变量；参数经过赋值影响 pass 时，记下的是被赋值的变量）。赋给有上限的变量时，和其他表达式一样在执行时检查（`(def (f n) max_leaves = n | rewrite)` 调用成 `(f 8)` 时这次运行报 `max_leaves is at most 6`）。

**名字参数**在解析时代入：每处调用得到一份把名字放进去的函数体，`(off name)` 的参数在调用处检查是不是开关（`unknown off name nope (the argument for n)`）。

**组参数**在函数体里是一个只读的组变量（`(load r)`、`(size r)`、单独写 `r`）。调用时把调用处那个组变量的候选组交给函数，所以读写检查在调用处做：`(def (f r) (load r))` 调用成 `(f t)` 而 `t` 没绑定时报 `prepass reads group variable t before it is bound`。`@inline` 函数共用调用处的组变量，组参数在展开时按名字代入，意思相同。

### 6.3 值、调用和闭包

值有这几种：数、一组候选、函数值、名字。

- **组值**：组变量（在文字里前面已经绑定过，`(save t)`、`t = ...`）、组参数、`@pipe` 的输入，单独写成一个名字时是一个值，给出它的候选组，不看当前输入。名字不满足这些条件时照旧读成 pass 名（所以写错的名字仍报 `unknown pass`）。`(load t)` 是函数调用，不是值。
- **以值开头的管线** `g | a | b` 是这个值依次经过各步的结果，即 `(b (a g))`；不以值开头的管线 `a | b` 是一个函数值。
- **函数值**：管线参数是 `group → group` 的函数值；`(p g)` 或 `g | p` 调用它，`(p (p g))` 调用两次。

**调用**：

- `a | (f x)` 由 `|` 填入输入；显式写全 `(f x g)` 时最后一个参数是输入，可以是组变量名、组参数，或括号里的一步（`(f x (lowbits | unshift))`：以值开头时是那个值经过各步，否则是这一步的输入经过各步，即 `lowbits | unshift | (f x)`）。
- 内置函数也可以显式给输入：`(lowbits t)`、`(mixed t)`、`(same r t)`；只在写满了参数、后面又是一个值时才这样读（`(if c a u)` 的 `u` 仍是可选的管线参数）。
- 写了参数的函数后面跟一个不是变量、函数或定义的名字时，也读成组变量（在外层绑定的、或写错的），由读写检查判断（`(f x u)` 没有绑定 `u` 时报 `reads group variable u before it is bound`，不报参数个数）；没有参数的函数后面跟这样的名字仍报 `takes no arguments`（`(lowbits x)`）。
- 不带 `@pipe` 的函数不能写在 `|` 后面（`twice is not @pipe, so | cannot give it its input`）：它的调用是一个值，写在管线开头、赋值右边或作显式输入，`u = (twice rewrite t)`。
- **隐式输入**：一步的参数里，少写了输入的函数取这一步的输入，所以 `(if (size <= k) p)` 里的 `size` 是 `(size <这一步的输入>)`、`(if (big 3) p)` 里的 `big` 同理。函数体是表达式时，它的顶层不在任何步骤里，没有这样的输入：那里的数值函数、返回数的函数、以数结束的管线都要写出输入（`size > k` 报 `size needs its input here`，写 `(size g) > k`、`(mixed g)`、`(g | rewrite | size)`）。

**管线参数是闭包**：传进去的管线带着它写下时所在的运行，即调用处的输入、组变量和参数。它在被调用的函数里每用一次就运行一次，但：

- 读写的是调用处的组变量，条件 `input` 指调用处的输入；
- 里面的参数（管线参数和数值参数）指写下它的那个函数的参数，参数再往下传时层层回到写下它的地方：`(def (f n) (g (if (size <= n) x)))` 里的条件在 `g` 里面运行，读的仍是 `f` 的 `n`；
- `smallest` 按文字算：写下它的地方外面的 `smallest` 看得到它里面的步骤，函数体里包住参数的 `smallest` 只看到参数返回的候选（第 5.4 节）。

没有名字的运行状态跟着它实际运行的位置走：`wins` 的计数、`fix` 的 `moved`、`scope` 的缓存，和内置的 `best`、`wins` 拿到管线参数时一样；所以 `(def (w p) (wins 3 p))` 里 `p` 中的 `smaller` 由 `w` 里的 `wins` 数到。存数的变量沿调用链动态查找（第 5.1 节），读的是它运行时的绑定。

组变量的读写检查对管线参数在调用处做：它可能在调用里的任何时候运行，也可能运行多次或不运行（同 `fix` 的体）。

### 6.4 运行与展开

**不带 `@inline` 的调用是一次运行**（第 1.1 节的函数也是）：

- 它是作用域：函数体里的赋值、`on`、`off` 在返回时撤销；函数体读得到调用处的绑定（动态作用域）。
- 它有自己的组变量和记录寄存器：调用处的组变量看不到（组参数除外），函数体里绑定的在返回后也看不到。
- 外面的 `smallest` 看不到函数里面，只看到调用给出的候选（调用是计算的步骤，第 5.4 节）；`wins`、`moved` 只看本次运行。
- 条件 `input` 在函数体里指调用时的主候选。在 `scope` 里调用时，单项 pass 仍共用那个 `scope` 的缓存。

**`@inline` 函数和 `let`** 不开新的运行，共享调用处的作用域、组变量、记录寄存器和 `smallest`：

- 函数体直接写成 `a | b` 时平铺进所在的序列（调用写成 `NAME` 或 `(NAME ARG ...)` 都是），里面的赋值作用到那条序列的末尾；写成 `(a | b)` 时是一条嵌套的序列，里面的赋值只在这里面有效。
- 没有数值参数、不带 `@pipe` 时在解析时展开：管线参数、组参数、名字参数代入，展开后的样子就是调用处的一部分（`(def @inline (g r p) p | (load r))` 调用成 `(g t rewrite)` 就是 `rewrite | (load t)`）。
- 有数值参数时不在解析时展开：调用时先求数值参数，带上自己的参数，函数体照样在调用处的作用域里运行；管线参数照样是闭包。组变量和赋值的检查、警告按展开后的样子在调用处做。
- 带 `@pipe` 时，每次调用把输入绑定到调用处组变量表里一个它自己的名字（`g#N`，用户写不出），函数体里的 `g` 读它，所以嵌套的调用互不覆盖。

要让赋值影响后面的步骤、共用组变量，或让外面的 `smallest` 看到里面的候选，用 `@inline`；要隔离，用不带属性的 `def`。

### 6.5 返回类型

返回类型就是函数体的类型，推出的签名的最后写着它：`(try_without name:name p:pipe g:group) group`、`(big k:num g:group) num`。

- 返回候选组的函数写在步骤位置；没有参数时写名字，有参数时写 `(NAME ARG ...)`。
- 返回数的函数只能写在要数的地方：`(if (big 3) p)`、`(filter (big 3))`、`keep = (big 3)`、表达式里；也可以作管线的最后一步（第 4.2 节）。输入没写时取这一步的输入，写了时是那一组候选：`(big 3 t)`、`(big 3 (lowbits | unshift))`。没有参数的返回数的函数写在括号里时，`(f)`、`(f t)`、`(f (a | b))` 是调用，`(f < 3)` 是表达式。
- 函数体是表达式时，求值不开新的运行，`@inline` 与否结果一样；函数体是以数结束的管线时，调用是一次运行（同返回候选的 `def`），不能带 `@inline`（报 `a function that gives a number is a run of its own, so it cannot be @inline or a let`）。所以 `(def @inline (f) lowbits | size)`、`(let f lowbits | size)` 报错。
- 函数体里的函数照常在空组上得 0，所以返回数的函数在空组上也得 0（除非函数体只读变量和参数）。
- 相邻步骤的类型按第 4.2 节相接。

### 6.6 名字和递归

- 函数名和变量、函数（内置的和已定义的 `def`）、宏、`let` 名不能重复（报 `the name of a pass, form or macro`、`the name of a variable or function`、`already a function`）。`let` 和 `def @inline` 可以重新定义已有的 `let` 名，之后的项用新的定义；`def` 不能重新定义 `let` 名（`already defined by let or def @inline`）。
- 第 1.1 节的 `pipeline`、`prepass`、`polish`、`rewrite`、`simba`、`sub/NAME` 只能被 `(def (NAME) P)` 或 `NAME=P` 替换：不带参数，不带 `@inline`；`sub/NAME` 的 `NAME` 要是第 11 节的名字之一。
- **不允许递归**：函数不能经过别的函数回到自己。函数只能调用在它之前定义的函数，调用处的管线参数也只能写已经定义的名字，所以 `def` 之间成不了环；能成环的只有经过运行时取定义的 `prepass`、`polish`，管线参数里的调用算在调用处（`(def (g p) p) prepass=(g prepass)` 报 `prepass reaches itself`）。`rewrite`、`simba`、`sub/NAME` 这一组内部本来就递归（在子项上），照旧；被这一组调用、又调用回这一组的 `def` 也算在组里。
- `egglog`、`reprint` 写在 `def` 里时，只有 `pipeline` 可以（经过别的函数）调用这个 `def`。

### 6.7 错误和警告

解析时报错（第 13 节有全部的检查）：参数名冲突、重复、用法矛盾、没用到、被赋值；未知的类型、属性；`@pipe` 的最后一个参数不是组、函数体不以值开头也不是表达式；返回数的管线带 `@inline` 或写成 `let`；函数体顶层的函数没写输入；调用处参数的个数和种类不对（报错附上签名）；不带 `@pipe` 的函数写在 `|` 后面；返回数的函数写在步骤位置（`f gives a number, not candidates`）、返回候选的函数写在表达式里（`f gives candidates, not a number`）或 `=` 左边（`f is a function and cannot be assigned`）；递归；读没绑定的组变量（每个 `def` 的函数体单独检查，组参数和输入算已绑定）。

只给警告：定义了却没用到的函数（`(def (f p n) ...) is never used`）；没写类型的参数只用在管线和组都合适的位置；组值写在 `|` 后面；以及第 13 节对每条管线做的那些检查，对每个 `def` 的函数体也单独做。

### 6.8 例子

每段是一个独立的例子：

```
(def (twice) rewrite | rewrite)
(def @inline (lb) lowbits | relate)
prepass=lb | twice | finish                  # 即 lowbits | relate | twice | finish

(def (try_without name p) (best 1 p ((off name) | p)))
prepass=(try_without relate rewrite)         # 即 (best 1 rewrite ((off relate) | rewrite))，在 try_without 的运行里

(def (hold r p) p | (union id (load r)))     # (hold r:group p:pipe g:group) group
prepass=(save t) | (hold t (lowbits | rewrite))

(def (f p) (save t) | p | (load t))
prepass=(save t) | (f ((load t) | rewrite))  # 参数里的 (load t) 读调用处的 t，f 最后的 (load t) 读 f 自己的 t

(def (with_budget n p) rewrites = n | p)
(def (if_small k p) (if (size <= k) p))
(def (f n) (if_small (n * 2) (rewrite | (filter (size <= n)))))
prepass=(f (size / 2)) | (with_budget 8 relate)   # n 是调用时输入大小的一半；filter 在 if_small 里运行，读 f 的 n

(def @inline (lim n p) split_runs = n | p)
prepass=(lim (size - 1) rewrite) | relate    # split_runs 的赋值作用到序列末尾，relate 也读到

(def @pipe (f p g) g | p)
(def (twice p g) (p (p g)))                  # 不带 @pipe：只能写全参数调用
(def @pipe (big k g) (size g) > k)           # (big k:num g:group) num
prepass=(f rewrite) | (save t) | u = (twice relate t) | (if (big 3) (load u))

(def (size_after) rewrite | size)            # 以数结束的管线：(size_after g:group) num
(def @pipe (h g) g | lowbits | size > 3)
(def @inline @pipe (k p g) g | p | (union id g))
prepass=(if ((t = rewrite | size) < size_after) (k rewrite t)) | (filter (h (lowbits | unshift)))
```

## 7. 表达式

### 7.1 求值

- 表达式在执行到它的那一刻、对当时的候选组求值，结果是一个数或 `none`。
- `if` 的条件对输入求值；`retry` 的条件对 `a` 的结果求值；`filter`、`any`、`all` 对每个候选单独求值；`fix`、`wins` 的次数在进入形式时求值，`best` 的个数在各支运行之后求值。
- 作条件用时，非 0 为真（`none` 为真）。
- 作次数用时，`none` 是不限。

### 7.2 运算

| 运算 | 规则 |
|---|---|
| `a + b`、`a * b` | 溢出或有一边是 `none` 时得 `none` |
| `a - b` | 饱和：小于 0 时得 0；`none - n` 是 `none`，`n - none` 是 0（`none - none` 也是 0） |
| `a / b` | 向下取整；`b` 为 0 时得 `none`（`none / 0` 也是）；`n / none` 是 0（`none / none` 也是），`none / n` 是 `none` |
| 比较 | 照常比较，`none` 大于所有整数，`none == none` |
| `!a` | `a` 为 0 时得 1，否则得 0 |
| `a && b`、`a \|\| b` | 得 1 或 0 |

### 7.3 数值函数

数值函数对当前候选组现算，什么都不存。**候选组为空时，数值函数都得 0**：没有候选可算。（`none` 只表示变量没赋值，数值函数不会得 `none`。）

**形状**（主候选的数）：`size`（节点数）、`vars`、`depth`、`mul`（乘积数）、`bitconst`（与常数的位运算数）、`arith_in_bit`（位运算下的算术数）、`shift`、`div`。

**性质**（1 或 0；除另有说明外看主候选）：

| 名字 | 为 1 时 |
|---|---|
| `opaque` | 有移位、除法或 `mulhi`，且它的重建大于 `tiny_size` 个节点（会运行 `prepass`） |
| `rebuilds` | 预处理会改变它（会运行 `prepass`） |
| `minimal` | 某个候选被证明最小：没有更小的项与它相等（`prove_minimal` 开着时才证明） |
| `mixed` | 位运算下直接有算术或常数 |
| `moved` | 上一个 `fix` 停在次数上，主候选还在变 |
| `input` | 它就是本次运行的输入：`pipeline` 里是 `simplify` 的输入，`prepass` 里是预处理的那个项，`polish` 里是那个候选；`rewrite`、`simba`、`sub/NAME` 里总是 0 |
| `tiny` | 至多 `tiny_size` 个节点 |
| `fits_split` | 至多 `split_size` 个节点 |
| `used_wide`、`used_clustered` | 有一个候选的 `used` 里有这一位（看整组） |
| `few_rewrites` | 它的 `rewrites` 至多 `unclustered_after` |
| `replaceable` | 整体有更小的 T-函数形式 |
| `abstracted` | 来源是抽象了子项的重建（`over_const_bitwise`、`over_shared_bitwise`） |
| `no_leaves` | 是没有叶子的线性区域 |
| `wide` | 是叶子多于 `max_leaves` 个的线性区域 |
| `const_bitwise` | 有与常数的位运算 |
| `cofactor` | 本次运行在重建 `poly_mba` 的线性余因子 |

性质之中，`opaque`、`rebuilds` 要跑一次 `prepass`，比较贵；其余只看项本身或候选的附带信息。

**带参数的函数**：
- `(size R)`：组变量 `R` 主候选的大小；`R` 为空或没绑定时得 0。
- `(same R)`：主候选和 `R` 的主候选相同时为 1；有一边为空时为 0。
- `(any C)`：有一个候选单独满足 `C`；`(all C)`：有候选，且每个都单独满足（`C` 是 `term->num`）。

比较照常比较这些 0：`size < (size r)` 在 `r` 为空时为假，`size > (size m)` 在 `m` 为空时（主候选不空）为真；空组上 `(0 < 1)` 照样为真。默认管线读的组变量在读时都不为空。

变量（第 10 节）在表达式里读当前绑定的值：`(if rerun_input ...)`、`(fix (restarts - 1) later)`、`(filter (size <= split_size))`。

**以数结束的管线**：管线的最后一步可以是给出数的步骤（数值函数、返回数的函数，可以带运算：`a | size > 3`），整条管线就给出一个数。在表达式里写在括号里，凡是要数的地方都能写：赋值右边 `x = (prepass | size)`、表达式参数 `(fix (prepass | size) p)`、比较和运算的一边 `((rewrite | size) < size)`、`def` 的数值参数、`filter`、`any`、`all` 的条件。括号里 `|` 之前的位置是一个数值函数或返回数的函数时，那仍是它的调用（`(f 3 a | b)` 是 `f` 的最后一个管线参数）；否则括号里有一个不在更深括号里的 `|` 时就是这种管线。

- 在当前输入上运行（以值开头的 `(t | rewrite | size)` 从那个值开始），各步是所在运行的步骤：读写所在运行的组变量和参数（`((t = rewrite | size) > 0)` 之后 `t` 可读），外面的 `smallest` 在它的计算步骤后面照样插 `note`，过了截止时刻各步照常跳过，最后的数在当时的候选组上算。管线本身是一个作用域，里面的赋值不漏出来。
- 在 `filter`、`any`、`all` 里对每个候选单独运行。
- 函数体顶层没有"这一步的输入"，那里的这种管线必须以值开头（`(size g) > (g | rewrite | size)`）。
- `--show-passes` 照写下的样子打印；`(mixed (lowbits | unshift))` 这样给数值函数显式写的管线输入打印成 `(lowbits | unshift | mixed)`，意思相同。

## 8. 带参数的候选组函数

下表中 `p`、`a`、`b` 是管线，`C` 是条件（`if`、`retry` 的是 `group->num`，`filter` 的是 `term->num`），`N`、`K` 是次数（`num`），`R` 是组变量。参数里有管线的是高阶函数；`a | b` 是序列，不是函数，列在这里是为了对照 `(seq ...)`。

| 函数 | 含义 | 空组、顺序 |
|---|---|---|
| `a \| b`、`(seq a b ...)` | 依次执行，前一步的候选交给后一步；是作用域 | — |
| `(union a b ...)` | 每个都在同一组输入上运行，输出按分支顺序连起来，去重时留先出现的 | 某支给出空组时只是不贡献 |
| `(best K a b ...)` | 同 `union`，再按大小排序（同样大小时保持原来的先后），保留最小的 `K` 个，至少 1 个。保留的主候选来自某个 alternative 时，记它一次 `won` | — |
| `(first a b ...)` | 依次运行，返回第一个非空、且与输入不同的结果；都没有就返回输入。"不同"比较项和来源 | — |
| `(fix N p)` | 重复 `p` 至多 `N` 次，主候选不再变化时停；停在次数上（还在变）时 `moved` 为 1 | 输入和结果都空算不变 |
| `(if C a)`、`(if C a b)` | 对输入求 `C`，真时运行 `a`，否则运行 `b`（省略时是 `id`） | — |
| `(retry C a b)` | 运行 `a`；`C` 对 `a` 的结果成立时，在原输入上运行 `b`，`b` 的主候选不比 `a` 的大时取 `b` | `b` 给出空组时取 `a`；`a` 给出空组、`b` 不空时取 `b` |
| `(filter C)` | 对每个候选单独求 `C`，只保留成立的 | — |
| `(smallest p)` | 宏（第 5.4 节）：运行 `p`；`p` 的文字里计算的步骤给出过比结果主候选严格更小的候选时，把其中第一个最小的放到结果最前面（去重） | 结果为空时原样返回 |
| `(smaller NAME p)` | 运行 `p`，主候选严格变小才采用，否则返回输入。采用时来源改为 `NAME`，记 `NAME/won`、`NAME/gain` | 输入或结果为空时返回输入 |
| `(wins N p)` | 重复 `p`，直到其中的 `smaller` 这一遍没有采用结果，或一共采用了 `N` 次 | `N` 为 0 时不运行 `p`，原样返回 |
| `(tag NAME p)` | 运行 `p`，记时间 `NAME/run`；主候选变了时记 `NAME/won/来源`，来源改为 `NAME` | — |
| `(cand NAME p)` | 一个预处理候选：`NAME` 是 `PRE` 的名字（第 12.2 节的 `pre`）且被关掉时给出空组；否则运行 `(bit_split_budget = cand_bit_splits \| p)`（所以也是作用域），结果来源都改为 `NAME`，记 `pre/NAME/made` | — |
| `(scope p)` | `p` 里对同一个项的各 pass 共用一个运行上下文（缓存）；是作用域 | — |
| `(regions p)` | 对每个候选：如果它是一个线性区域，叶子先用 `rewrite` 重建，整体用 `p` 的主候选；否则对它的操作数用 `rewrite` | — |
| `(again p)` | 运行 `p`；主候选在"位运算的算术叶子"处有变化时，对它再做一次 `rewrite`，变小才保留 | — |
| `(save R)`、`(load R)` | 第 5.5 节：`(save R)` 即 `R = id`；`load` 一个没绑定的组变量给出空组，可以反复读 | — |
| `(clear R)` | 打开一个空的记录寄存器 `R`（第 5.5 节），原样返回 | — |
| `(note R)` | 当前组里第一个最小的候选比最新打开的 `R` 里的严格更小（或 `R` 是空的）时记进去，原样返回；过了截止时刻和其他计算的步骤一样跳过，但不算截断（`@uncounted`） | 空组、没有打开的 `R` 时什么也不记 |
| `(take_min R)` | 关上最新打开的 `R`：它的候选比当前组的主候选严格更小时放到最前面（去重），否则原样返回 | 当前组为空时原样返回 |
| `(label R)` | 只做统计：每个候选记 `stats::label`，与组变量 `R` 的主候选来源不同时记 `pre/来源/differs`、`pre/来源/gain`；`--trace` 时打印候选 | — |
| `(egglog LABEL)`、`egglog` | 一轮 egglog：所有候选并入一个 e-graph，饱和，提取出一个候选。统计计在 `egglog/LABEL` 下 | — |

`tag`、`label`、`smaller`、`cand` 记的统计不影响结果；它们改的来源会影响结果（第 2.2 节）。

## 9. 不带参数的候选组函数（pass）

这些函数习惯上叫 pass。按调用方式分四种：整组、单项、alternative、polish（第 4.3 节，由签名决定）。

### 9.1 整组

对整组候选操作。组为空时，除 `none` 外都原样返回。

| pass | 含义 |
|---|---|
| `id` | 原样返回 |
| `none` | 给出空组 |
| `prepass` | 对主候选运行 `prepass` 管线，用它的结果替换整组：第一个是主重建，其后是要一起并入 e-graph 的 |
| `polish` | 对每个候选单独运行 `polish` 管线（每次是一次单独的运行），结果的主候选变小时替换 |
| `take_minimal` | 第一个被证明最小的候选（`minimal`）；没有就原样返回 |
| `reprint` | 主候选打印成中缀再读回，只留这一个 |
| `within` | 当前的 `rewrites` 用完时给出空组，否则原样返回 |
| `pre_done` | 预处理的结尾：统计保留的候选，来源改为 `pre/来源`；主候选与输入相同时，按组变量 `t0` 里输入原来的写法给出 |

### 9.2 单项

对每个候选单独运行，用结果替换它；没有结果或结果不变时保留原候选（alternative 除外）。

| pass | 含义 |
|---|---|
| `lowbits` | 已知位推理：只碰已知位的位运算改成加法、低位截断、按求值确定的低位 |
| `unshift` | 把 `c·(a >> s)` 等写成掩码形式，使区域成为半线性的 |
| `tfunc_whole` | 整个项换成更小的 T-函数形式（≤ `tfunc_max_vars` 个变量）；不适用时没有结果 |
| `tfunc` | 对子项做同样的替换 |
| `rewrite` | 运行 `rewrite` 管线（带缓存） |
| `rewrite_top` | 同 `rewrite`，统计分开计 |
| `cluster_regions`、`cluster_top` | 对结果的每个区域做 `clustered` 式的分组重建；`cluster_top` 只是统计名不同 |
| `relate` | 把位运算的算术叶子换成占位变量，加上它们之间的零关系再重建 |
| `unify_operands` | 统一位运算操作数的写法，让更多叶子能共享 |
| `recombine` | 把 `c·P1·Q1 + c·P2·Q2` 合回一个乘积（还原 `a·b` 的拆分） |
| `cut_products` | 按另一个因子的尾零截断乘积因子里的常数 |
| `shifted_xor` | `2^k·(a ^ K) + c` 写成 `(2^k·a) ^ (2^k·K + c)` |
| `simplify_rebuilt` | 只用于重建结果的 `lowbits` 部分（截断乘数等） |
| `finish` | 重建候选的收尾：`recombine`、`cut_products`、`shifted_xor`，再 `lowbits` |
| `halve` | `2^k·a + c` 形式的操作数拆半：`2^k·(a op b) + (c op d)` |
| `over_const_bitwise`、`over_shared_bitwise` | 把与常数的位运算、或共享的位运算子项抽象成变量重建，再代回 |
| `over_products` | 把乘积抽象成变量重建，再代回 |
| `split_bits` | 按单个变量位分情况重建，还原 Hikari/OLLVM 式的选择 |
| `drop_identities` | 去掉加 0、乘 1 |
| `rebuild` | 不带 `relate` 的一次重建（`lowbits`、`unshift`、`rewrite`、`cluster_regions`、`tfunc`） |

### 9.3 Alternative

也是单项函数，但对候选整体运行。找不到形式时**不给出候选**（而不是保留原候选）；给出的候选来源是自己的名字，所以 `best` 能记哪一个胜出。

| pass | 含义 |
|---|---|
| `simba` | 运行 `simba` 管线 |
| `small_blocks` | 按合取基里的块（≤ 3 个叶子）逐块重建 |
| `wide_blocks` | 宽区域的分块重建；被保留时置 `used` 的 wide 位 |
| `poly_mba` | 多项式 MBA 的展开、约化和因式分解 |
| `drop_unused` | 把值不依赖的叶子置 0 后重建 |
| `clustered` | 按用到的叶子把项分组，各组分别重建；被保留时置 `used` 的 clustered 位 |
| `peel`、`peel_clustered` | 剥掉一个项再重建其余部分 |
| `semi_linear` | 带常数掩码区域的逐位重建 |
| `rebuild_values` | 按区域在 {0,1}^n 上的取值重建 |
| `common_multiple` | 提出系数相近的公倍数 `c·(v_1 + ... + v_k)` |
| `related_leaves` | 加上叶子间零关系的小倍数后重建 |
| `one_wide_term` | 整个区域写成一个位运算项 |

### 9.4 Polish

写作 `polish/NAME`，单项函数，用在 `polish` 函数里：`push_not`、`join_constants`、`join_linear`、`over_const_bitwise`、`over_shared_bitwise`、`over_products`、`recombine`、`shift_cases`、`decompose`、`factor`。`--passes` 的 `polish=a,b,...` 是这些名字的简写（第 12 节）。

## 10. 变量

### 10.1 开关

每个内部 pass 是一个开关变量，值为 0 时它被关掉：在一串步骤里返回输入，作为 alternative 时不给出形式。大多数同时也是 pass 名；`poly/masked`、`semi/*` 只是内部步骤：

`lowbits unshift tfunc_whole relate tfunc unify_operands recombine cut_products shifted_xor simplify_rebuilt cluster_regions simba small_blocks wide_blocks poly_mba poly/masked rebuild_values common_multiple related_leaves one_wide_term semi_linear drop_unused clustered peel peel_clustered semi/grouped semi/peel_grouped semi/shapes semi/pairs semi/peel_shapes semi/semi_split semi/scaled semi/bit_split semi/short_consts`

`default.pipe` 关掉的是 `semi/peel_shapes`。

其他开关：

| 名字 | 默认 | 含义 |
|---|---|---|
| `cut` | 0（默认 `pipeline` 里设成 1） | 开着时，因时限跳过的步骤把整次运行记为截断 |
| `rerun_input` | 1 | 结果是 `mixed` 时带上原输入重跑第一轮 |
| `prove_minimal` | 1 | 尝试证明候选最小 |
| `relate_parts` | 1 | `relate` 对叶子多于 `relate_leaves` 的区域也按部分处理；不带 `clustered` 的重建里设成 0 |

### 10.2 运行

| 名字 | 默认 | 含义 |
|---|---|---|
| `restarts` | 来自 `-m` | 总轮数；默认 `pipeline` 写 `(fix (restarts - 1) later)`，因为第一轮单独写出。从 Rust 直接进入的运行没有命令行，它和 `iter_limit` 是 `none` |
| `iter_limit` | 来自 `-i` | 每轮 egglog 重复调度几次 |
| `keep` | 2 | 预处理保留几个候选；读出时至少是 1（`keep = 0` 读作 1） |
| `extra` | 2 | 预处理还在改变结果时，额外跑几轮 |
| `printed` | 2 | 从打印结果再跑几轮（0 不跑）；默认 `pipeline` 写 `(fix (printed - 1) later)` |
| `match_limit` | 64 | back-off 调度：一条规则每次运行最多匹配几次，超过就被禁用；下一轮 egglog 起生效 |
| `ban_length` | 3 | back-off 调度：被禁用的规则先停几次运行；下一轮 egglog 起生效 |

### 10.3 预算与时限

| 名字 | 默认 | 含义 |
|---|---|---|
| `rewrites` | `none` | 剩下的未缓存 `rewrite` 调用次数，用完后 `rewrite` 原样返回（第 5.1 节） |
| `bit_split_budget` | `none` | 剩下的 `bit_split` 拆分对数；每个 `cand` 设成 `cand_bit_splits` |
| `time_limit` | `none` | 截止时刻，赋值时从此刻起计毫秒（第 5.3 节）。bench 用 `-t` 乘以它的 `--time-limit` 比例（默认 0.8）设置，比例为 0 时传 `none`；写在 `--passes` 里的在它之后，所以优先。`time_limit = 0` 是 0 毫秒，立即到期 |

### 10.4 限值

| 名字 | 默认 | 含义 |
|---|---|---|
| `semi_leaves` | `max_leaves` | 半线性区域最多几个叶子才重建 |
| `relate_leaves` | `max_wide_leaves` | `relate` 只处理叶子不多于此的区域 |
| `unclustered_relate_leaves` | 10 | 不带 `clustered` 的重建里，`relate` 只处理这么多叶子以内的区域 |
| `unclustered_rewrites` | 256 | 不带 `clustered` 的重建最多调用 `rewrite` 的次数，超过就放弃 |
| `unclustered_after` | 1024 | 其他重建的 `rewrite` 次数不超过此值时，才尝试不带 `clustered` 的重建 |
| `unified_rewrites` | 128 | 统一操作数后重建的最多 `rewrite` 次数 |
| `related_rebuilds` | 8 | `related_leaves` 最多重建几种组合 |
| `related` | 4 | `relate` 每个区域最多试几个算术叶子 |
| `bit_splits` | 4 | `bit_split` 每个区域最多重建几种拆分 |
| `cand_bit_splits` | 8 | 每个预处理候选最多几对 `P op Q` |
| `splits` | 4 | `split_bits` 对一个项最多试几个变量位 |
| `split_depth` | 2 | `split_bits` 最多嵌套几层 |
| `split_runs` | 16 | 一次 `split_bits` 最多几次重建 |
| `split_size` | 64 | `split_bits` 只处理不大于此的第一次重建 |
| `split_max_unknown_bits` | 2 | `split_bits`：乘积因子最多几个未知位才按位分情况 |
| `block_leaves` | 12 | `small_blocks` 最多处理几个叶子 |
| `block_combos` | 32768 | `small_blocks` 穷举的组合数上限，也是 `wide_blocks` 搜索的步数上限 |
| `block_max_block` | 3，上限 5 | `small_blocks`：一个块最多几个叶子；系数从至多这么多个 1 的点插值，每块试全部 `2^(2^k)` 个真值表 |
| `block_descent_rounds` | 4 | `small_blocks`：组合太多、不能穷举时，坐标下降最多几轮 |
| `block_spread_points` | 8 | `small_blocks`：完整检查前先查几个分散的点，多数区域早早被排除；不改变结果 |
| `cluster_depth` | 2 | `clustered` 最多嵌套几层 |
| `poly_builds` | 512 | `poly_mba` 穷举选择时最多构造几个乘积，之后每层只取第一种 |
| `poly_branch_monos` | 128 | 展开的单项式多于此时，从一开始就每层只取第一种 |
| `polish_rewrites` | 2000 | 一次 `polish` 最多几次未缓存的 `rewrite` |
| `polish_wins` | 8 | 默认 `polish`（和 `polish=a,b,...`）最多采用几次 `smaller` 的结果 |
| `tiny_size` | 3 | 不大于此的重建不再细找：函数 `tiny`，`opaque` 要求重建大于它 |
| `max_leaves` | 6，上限 6 | 线性区域最多几个叶子才按 {0,1}^n 上的值重建（真值表是 `u64`） |
| `max_wide_leaves` | 16，上限 64 | 宽区域最多几个叶子才整体求值（`drop_unused`、`relate`、`peel`；用到的叶子是 `u64` 掩码） |
| `lowbits_max_bits` | 18，上限 63 | `lowbits`：一个子项最多枚举几个叶子位 |
| `lowbits_max_context_bits` | 18，上限 63 | `lowbits`：在上下文里证明时最多枚举几个叶子位 |
| `lowbits_narrow_context_bits` | 12 | `lowbits`：多于这么多叶子位的证明还要用 `lowbits_wide_budget` |
| `lowbits_max_try` | 256 | `lowbits`：枚举或在上下文里证明的子项最大多大 |
| `lowbits_max_values` | 4 | `lowbits`：子项最多几个不同的值时，才试着在上下文里换成其中之一 |
| `lowbits_max_product_bits` | 4 | `lowbits`：没有变量移位时，只枚举值由叶子低这么多位决定的含乘积子项 |
| `lowbits_budget` | 67108864 | `lowbits`：一次调用所有枚举的求值步数 |
| `lowbits_wide_budget` | 8388608 | `lowbits`：多于 `lowbits_narrow_context_bits` 位的证明的求值步数 |
| `lowbits_max_low_rebuild` | 64 | `cut_products`：截断常数后重建的乘积因子最大多大 |
| `lowbits_refine_bits` | 2 | `lowbits`：`refine_low` 在已知位之外多枚举几位 |
| `lowbits_max_refine_bits` | 12，上限 63 | `lowbits`：`refine_low` 总共最多枚举几个叶子位 |
| `lowbits_refine_budget` | 4194304 | `lowbits`：`refine_low` 一次调用的求值步数 |
| `lowbits_max_factor_terms` | 4 | `over_products`：多于这么多项的因子不展开 |
| `poly_max_monos` | 4096 | `poly_mba`：乘出来的积最多几个单项式，超过就不展开 |
| `poly_monos_per_node` | 4 | `poly_mba`：展开的单项式多于项的节点数的这么多倍时不重建 |
| `poly_factor_tries` | 3 | `poly_mba`：重建整个多项式时试几个公因子（下层只试一个） |
| `poly_max_factor_monos` | 64 | `poly_mba`：最多几个单项式的多项式才分解因式，也是按约化形式再重建一次的上限 |
| `poly_max_factor_vars` | 12 | `poly_mba`：最多几个合取的多项式才分解因式 |
| `poly_max_pivots` | 4 | `poly_mba`：分解因式时最多试几个主元合取 |
| `poly_max_roots` | 16 | `poly_mba`：系数方程的根多于此时只留几个可能的根 |
| `poly_max_factor_steps` | 4096 | `poly_mba`：分解因式时最多试几种根的组合 |
| `poly_max_solutions` | 8 | `poly_mba`：一个主元最多给出几种分解 |
| `poly_max_shifted` | 4 | `poly_mba`：最多几种分解把因子加减常数、和线性余项并列 |
| `poly_max_shifted_monos` | 4 | `poly_mba`：加减常数的因子最多几个单项式 |
| `poly_shifted_rest_ratio` | 2 | `poly_mba`：加减常数的分解旁边，线性余项最多是 `poly_max_shifted_monos` 的几倍个单项式 |
| `poly_max_atoms` | 4 | `poly_mba`：按掩码展开时最多把位分成几组 |
| `poly_max_masked_monos` | 16 | `poly_mba`：按掩码展开最多几个单项式（或普通展开的 `poly_masked_monos_ratio` 倍） |
| `poly_masked_monos_ratio` | 2 | `poly_mba`：按掩码展开也可以有普通展开的这么多倍个单项式 |
| `poly_max_masked_size` | 20 | `poly_mba`：只有一个两边都带常数的乘积时，按掩码展开的项最大多大 |
| `common_multiple_min` | 4 | `common_multiple`：提出的 `c` 的绝对值至少多大 |
| `common_multiple_tries` | 2 | `common_multiple`：最多试几个 `c` |
| `overlap_max_values` | 4 | `overlapping_terms`：表里不同的非零值多于此时不搜索 |
| `overlap_max_choices` | 16 | `overlapping_terms`：一个点的值是几组系数之和时，最多试几种取法 |
| `overlap_max_terms` | 3，上限 63 | `overlapping_terms`：最多搜几个位运算项的和 |
| `decompose_max_vars` | 5 | 找最短位运算式时，最多几个变量的真值表才试 `g(A) op h(B)` 分解（`decompose`） |
| `decompose_min_free_size` | 10 | `decompose`：要胜过的大小至少这么大时，才把自由点两种取值都试 |
| `decompose_max_free_classes` | 4，上限 63 | `decompose`：一边最多枚举几类自由点 |
| `decompose_fill_max_vars` | 3 | `decompose`：一边最多几个变量才填自由点 |
| `decompose_xor_max_shared` | 2 | `decompose`：`^` 两边最多共用几个变量，才把它们的函数异或进两边 |
| `related_leaves_max_arith` | 4 | `related_leaves`：最多几个和区域其他叶子相关的算术叶子 |
| `relate_max_written_out` | 2 | `relate`：试过 `related` 个算术叶子后，再试几个区域里也展开写出的叶子 |
| `relate_max_free_product` | 20 | `relate`：不是位运算操作数的乘积叶子最大多大才试 |
| `relate_max_parts` | 8 | `relate`：按部分处理宽区域时最多试几个算术叶子 |
| `relate_wide_max_percent` | 90 | `relate`：宽区域里没有叶子或项消掉时，结果至多是区域大小的百分之几才保留 |
| `unify_operands_max_leaves` | 8，上限 63 | `unify_operands`：算术操作数最多几个叶子才按 {0,1}^n 上的值比较 |
| `memo_contexts` | 4 | `rewrite`、`simba_memo`、`relate` 的缓存每个键最多存几个结果，多了丢最早的（0 不缓存） |
| `join_constants_max_leaves` | 3 | `join_constants`：两个叶子组合起来和常数一起重建时，最多几个叶子 |
| `join_constants_max_sets` | 10 | `join_constants`：每个区域最多几次和常数一起的重建 |
| `join_linear_max_groups` | 12 | `join_linear`：区域最多几个叶子组才在组间移动叶子 |
| `join_linear_near_slack` | 4 | `join_linear`：一次移动最多多出几个节点，还能接着再移一次 |
| `join_linear_near_moves` | 3 | `join_linear`：最多几个这样的移动接着再移一次 |
| `join_linear_max_near_groups` | 8 | `join_linear`：区域最多几个叶子组才接着再移一次 |
| `shift_cases_depth` | 2 | `shift_cases`：最多嵌套按几个变量移位量分情况 |
| `shift_cases_max_size` | 64 | `shift_cases`：只处理不大于此的项（每个移位量最多重建 `2w` 种情况） |
| `shift_cases_amounts` | 2 | `shift_cases`：每层最多按几个移位量分情况 |
| `used_leaves_budget` | 33554432 | 宽区域在 {0,1}^n 上求值（`used_leaves`、`peel`）最多多少条指令乘点数 |
| `peel_min_size` | 16 | `peel`：区域的大小至少是叶子数的这么多倍才试 |
| `peel_spread_points` | 16 | `peel`：建位真值表之前，区域先要在几个分散的点上像位运算 |
| `wide_blocks_max_term_leaves` | 10，上限 63 | `wide_blocks`：一项最多几个叶子才展开 |
| `wide_blocks_max_block` | 10，上限 63 | `wide_blocks`：一个块最多几个叶子才重建成一项 |
| `wide_blocks_steps` | 4096 | `wide_blocks`：每个块、每个乘数找真值表的搜索步数 |
| `wide_blocks_max_tables` | 4096 | `wide_blocks`：不多于 6 个叶子的块最多收集几个真值表 |
| `wide_blocks_max_wide_tables` | 16 | `wide_blocks`：多于 6 个叶子的块最多收集几个真值表（按不相交分解写出，慢） |
| `wide_blocks_max_functions` | 64 | `wide_blocks`：每个块留几个最小的真值表给块间的搜索 |
| `wide_blocks_cache_size` | 4096 | `wide_blocks` 的线程级缓存最多存几个区域，满了清空 |
| `wide_blocks_descent_rounds` | 4 | `wide_blocks`：分支定界之前坐标下降最多几轮 |
| `wide_blocks_min_ratio` | 2 | `wide_blocks`：区域小于各块最小项大小之和的这么多倍时跳过（差不多已是块的形式） |
| `shapes_max_size` | 15，上限 15 | `semi/shapes`、`semi/pairs`：带自由常数的位运算式最大多大（第 15 层的表约 100 MB） |
| `pairs_max_groups` | 8 | `semi/pairs`：区域最多几个位组 |
| `pairs_budget` | 500000 | `semi/pairs`：一次调用最多检查几个式子 |
| `pairs_max_size` | 12 | `semi/pairs`：两个式子的大小之和最大多大 |
| `pairs_max_scales` | 12 | `semi/pairs`：最多试几个系数（从小的开始） |
| `pairs_max_carries` | 4096 | `semi/pairs`：进位 DP 每一位最多几个进位，超过就放弃 |
| `semi_split_max_combos` | 64 | `semi/semi_split`：每个集合最多试几种其他集合常数的组合 |
| `semi_half_flips` | 2 | `semi_linear`：最多几个位组把 `-2^(r-1)` 也读成 `+2^(r-1)` |
| `semi_max_merges` | 16 | `semi_linear`：按高位合并位组时最多枚举几种 |
| `semi_max_code_groups` | 4 | `semi_linear`：最多几个位组用常数叶子编码（每种编码都试） |
| `tfunc_max_vars` | 3，上限 4 | `tfunc`：子项最多几个变量（或位运算原子）才查表（求值点是定长数组） |
| `tfunc_max_size` | 7 | `tfunc`：查找表里的式子最大多大 |
| `tfunc_points` | 24，上限 24 | `tfunc`：查表时在几个点上求值（值是定长数组） |
| `tfunc_max_try` | 256 | `tfunc`：最大试多大的子项（大的很少能换，证明也贵） |
| `tfunc_max_carries` | 64，上限 128 | T-函数证明（`tfunc`、`lowbits`）：最多几个进位（进位状态是 `u128`） |
| `tfunc_max_states` | 512 | T-函数证明：每一位最多几个可达的进位状态，超过就放弃 |
| `tfunc_max_factor` | 255 | T-函数证明：展开成加法器的常数乘数（或它的相反数）最大多大 |
| `minimal_points` | 64 | 最小性证明：在几个点上比较项和更小的项 |
| `minimal_lanes` | 16，上限 16 | 只含 `+ - * & \| ^ ~ neg` 的最小性证明：低位值向量有几个点（定长数组） |
| `minimal_budget` | 2097152 | 只含 `+ - * & \| ^ ~ neg` 的最小性证明：最多组合几对项 |
| `minimal_max_vars` | 3，上限 31 | 枚举的最小性证明：多于 `2k - 1` 个节点的项最多几个变量（变量集是 `u32`） |
| `minimal_max_size_4bit` | 7 | 只含 `+ - * & \| ^ ~ neg` 的最小性证明：在 4 位里证明的项最大多大 |
| `minimal_max_size_8bit` | 5 | 只含 `+ - * & \| ^ ~ neg` 的最小性证明：在 8 位里证明的项最大多大 |

`lowbits_budget`、`lowbits_wide_budget`、`lowbits_refine_budget` 是普通变量（每次 `lowbits` 调用从它们开始计数），不是第 5.1 节的预算。`poly_mba` 的变量在每次展开开始时读一次；`poly_factor_tries` 只用于整个多项式那一层，下层总是只试一个公因子。
`decompose_max_vars`、`decompose_min_free_size`、`decompose_max_free_classes`、`decompose_fill_max_vars`、`decompose_xor_max_shared` 决定最短位运算式的搜索；线程级的真值表缓存按这五个值分开存，所以不同作用域里的不同值各建一份表。`memo_contexts` 只决定缓存留多少结果，不改变结果，所以不记入缓存读过的变量。
`wide_blocks_cache_size` 和 `memo_contexts` 一样只决定缓存留多少，不记入读过的变量；`wide_blocks` 的缓存键里有全部限值的哈希。带自由常数的位运算式按大小逐层建表，进程内共用；表里的式子与 `shapes_max_size` 无关，只是最大那一层的式子不当操作数，不存它们的真值表列表，所以值小时少建几层，值大时补上那一层的列表再接着建。
`tfunc` 的查找表进程内共用，按位宽、变量数和 `tfunc_max_vars`、`tfunc_max_size`、`tfunc_points` 分开建，所以不同作用域里的不同值各建一份，正常运行只建默认那一份；没用到的求值点上变量都是 0，值和第 0 个点相同，不改变查表的结果。`tfunc_max_carries`、`tfunc_max_states`、`tfunc_max_factor` 也决定 `lowbits` 在上下文里的证明，每次 `lowbits` 调用读一次。

## 11. `sub/NAME`

单项 pass 重建子项时调用的管线，默认是 `rewrite`（带缓存）或 `rebuild`（直接一次重建）。

| 名字 | 默认 | 用于 |
|---|---|---|
| `sub/cluster` | `rewrite` | `clustered` 的每一组，以及没变小的组里的每一项 |
| `sub/relate` | `rewrite` | `relate` 处理过的区域、缩小后的整个区域、取反的叶子 |
| `sub/bit_split` | `rewrite` | `bit_split` 的两边 |
| `sub/halve` | `rewrite` | `halve` 拆出来的操作数 |
| `sub/drop_unused` | `rewrite` | 置 0 了无用叶子的区域 |
| `sub/recombine` | `rewrite` | 合回的乘积的因子和改动过的区域 |
| `sub/polish` | `rewrite` | `join_constants`、`join_linear` 合并后的组 |
| `sub/low_factor` | `rewrite` | 按另一因子尾零截断了常数的乘积因子 |
| `sub/poly` | `rewrite` | `poly_mba` 展开所用的叶子，以及含与常数位运算的因子 |
| `sub/over_products` | `rebuild` | `over_products` 的各种情况 |
| `sub/split_bits` | `rebuild` | `split_bits` 的各种情况 |
| `sub/over_bitwise` | `rebuild` | `over_const_bitwise`、`over_shared_bitwise` 的项 |
| `sub/shift_cases` | `rebuild` | `shift_cases` 的各种情况 |

## 12. `--passes` 和命令行

`--passes` 的值是若干**项**，依次作用在 `src/default.pipe` 之上（`default.pipe` 本身也是这样一串项）。

### 12.1 分项

- `;` 总是分项。
- 括号外的空白：后面一段以 `KEY=`、`KEY+=`、`KEY-=`、`(let` 或 `(def` 开头，且前一段不以 `|` 结尾时，开始新的一项，否则接在上一项后面。所以 `prepass=a | split_runs=4 | b` 是一项，`prepass=a split_runs=4` 是两项。
- `#` 到行尾是注释。

### 12.2 项

| 项 | 含义 |
|---|---|
| `NAME=VALUE` | 入口程序里 `pipeline` 前的一步赋值。值同管线里的写法，可以是表达式。项里的空格只在后一段不像新的一项（不以 `KEY=` 开头）时才接在这一项里：`keep=keep + 1` 是一项（`Display` 就这样写），`keep=keep +1` 也是；要稳妥就不写空格 |
| `off=a,b`、`off+=a`、`off-=a` | 也是赋值：`off+=a` 是 `a = 0`，`off-=a` 是 `a = 1`，`off=a,b` 是把内部 pass 都设成 1 再关 `a`、`b` |
| `pipeline=P`、`prepass=P`、`polish=P`、`rewrite=P`、`simba=P`、`sub/NAME=P` | 替换这条管线的定义：`(def (NAME) P)` 的简写 |
| `polish=a,b,...` | 全是 polish pass 名时：依次尝试这些 `polish/NAME`，变小才保留，有一个变小就重来，至多保留 `polish_wins` 次 |
| `(let NAME P)` | 定义名字（第 6.1 节）。`default.pipe` 定义的名字（`first_round`、`later`、`gates`、`rebuild_main`……）也能用 |
| `(def [@inline] [@pipe] (NAME PARAM ...) P)` | 定义函数（第 6 节） |
| `file=PATH` | 在此处读入文件里的各项 |
| `pre=a,b`、`pre+=`、`pre-=` | 造哪些预处理候选：`unified no_wide split_bits halve_first over_products over_const_bitwise over_shared_bitwise halve_input unclustered` |
| `schedule=...`、`schedule+=`、`schedule-=` | 每轮 egglog 的步骤，逗号分隔的 `run:RS`（back-off 调度）、`once:RS`、`sat:RS`（饱和），`RS` 是 `default-ruleset canonicalization constant-folding analysis identity-zero-element simplify` 之一 |

赋值和 `off` 项按出现顺序排进入口程序；定义项（管线、`let`、`def`、`pre`、`schedule`）在读到时生效。`--show-passes` 怎样写出 `def` 见第 6.1 节。

命令行的 `-m N`、`-i N` 也是入口程序里的赋值（`restarts = N`、`iter_limit = N`）；`-n`（数值类型）决定建哪个 egglog 程序，不是变量。

## 13. 检查与警告

读完 `--passes` 后检查，出错时拒绝整个设置：

- 名字：未知的变量、函数、`on`/`off` 名、`sub/NAME`、规则集，报错并列出已知的名字。名字里的 `-` 读作减号，没法单独报错；解析出错时，如果写了 `a-b` 这样的词，错误后面加上"`a-b` 读作 `a - b`，名字用 `_`"，`a_b` 是已知名字时提示写 `a_b`。
- 类型，照签名（第 4.3 节；`def` 的签名见第 6.5 节）检查，报错时附上签名：步骤位置写了数值函数或变量（`mixed gives a number, not candidates: (mixed t:term) num`），表达式里写了候选组函数（`egglog gives candidates, not a number`）；参数的个数、种类（表达式、管线、组变量、名字）不对（`retry takes an expression and two pipelines: (retry c:group->num a:pipe b:pipe g:group) group`）；没有参数的函数写了参数；给出数的步骤接在 `|` 前面；以数结束的管线写在要候选的地方，或括号里的管线写在要数的地方却不以数结束；不带 `@pipe` 的函数写在 `|` 后面；函数体顶层的函数没写输入。
- 赋值（第 5.6 节）：给函数、参数赋值；值超过变量的上限；开关赋 `none`（开关只收数，0 是关）；右边的类型和左边不合（存数的变量给了候选，组变量给了数，报错写出两边）；组变量和存数的变量同名（`(save keep)`、`keep = rewrite`）。条件里写了 `=`（`(if (size = 3) ...)`）报 "an assignment is a step; compare with =="。
- 定义（第 6 节）：`let`、`def` 名和变量、函数、宏同名，`def` 重新定义已有的 `let`、`def` 名，`let` 重新定义 `def` 名；第 1.1 节的函数带参数或 `@inline`，未知的 `sub/NAME`；未知的属性、类型；`def` 的参数和已有的名字同名或重复、用法矛盾、没用到；`@pipe` 函数的最后一个参数不是组、函数体不以值开头也不是表达式；返回数的管线带 `@inline` 或写成 `let`。`(off NAME)` 的名字参数在调用处检查是不是开关。
- `extern` 写在 `src/builtins.pipe` 以外。
- 旧写法报错并提示新写法：`(with KEY=VALUE ... p)`（提示 `(KEY = VALUE | ... | p)`，它的 `bit_splits` 是 `bit_split_budget`）、`(time-limit N)`（提示 `time_limit = N`、`time_limit = none`）、条件名 `true`（提示 `1`，只在有候选时为真的写 `(any 1)`）、单名写法 `save/t`、`off/NAME`、`egglog/LABEL`、`seq(a,b)` 语法。`with` 外面的 `KEY=VALUE` 就是赋值 `KEY = VALUE`，不报错。
- 签名带 `@simplify_only` 的函数（`egglog`、`reprint`）只能出现在 `pipeline` 里：只有 `simplify` 的运行才有 e-graph。写在 `def` 里时，只有 `pipeline` 可以（经过别的函数）调用这个 `def`。
- 函数不能经过别的函数回到自己（第 6.6 节）。调用关系：`prepass` pass 和函数 `opaque`、`rebuilds` 调用 `prepass`；`polish` pass 调用 `polish`；单项 pass、`regions`、`again` 调用 `rewrite`、`simba`、`sub/NAME` 这一组；写出 `def` 名就调用它，调用处的管线参数里的调用算在调用处。
- 组变量的读（`load`、`label`、`size`、`same`、组值）前面必须有可能先执行的、绑定它的 `(save R)` 或 `R = p`（`R = p` 先算右边，所以 `t = (load t)`、`t = t` 报错；`t = u` 是读 `u`）。每个 `def` 的函数体单独检查（它有自己的组变量，组参数和输入算已绑定），有名字参数的按每种调用代入后的样子检查；`let`、`@inline` 按展开后的样子在调用处检查。管线参数读写调用处的组变量，在调用处检查，当作可能运行多次的体。按执行顺序算：`if` 的两支都算，`retry` 的条件在 `a` 之后，`best` 的个数在各支之后；`fix`、`wins`、`regions` 的体会重复执行，体里任何地方的绑定对整个体都算。这条检查找的是写错名字和顺序，不保证运行时一定有值。

以下只给警告：`eggy1` 和 `bench` 的父进程打印到 stderr，`bench --one` 子进程不打印。

- `--passes` 里定义了却没用到的 `let`、`def`（`(def (f p n) ...) is never used`）。
- 没注解的 `def` 参数只用在管线和组都合适的位置（`t = r`、函数体就是 `r`），按管线算（`parameter r is used only where a pipeline or a group fits`）。

以下几条对每条管线和每个 `def` 的函数体单独检查：

- 绑定了却从不读的组变量；同一层又绑定了一次、中间没读的死存储（写在 `if`、`cand`、`first` 的后几支、`retry` 的 `b` 或循环体里的绑定不和外面的比较，所以 `(save t) | (if c (save t))` 这种先存默认值再覆盖的写法不算）。
- 赋值（包括 `(on NAME)`、`(off NAME)`）是所在序列（或整条管线）的最后一步：什么也影响不到。
- 同一条序列里同一个变量连赋两次，中间只有赋值，也没有读它。
- 组值写在 `|` 后面（`a | t`、`a | (lowbits t)`）：丢掉前面的结果（`X drops its input`）。`(load t)` 和 `@inline @pipe` 调用生成的输入不警告。

默认管线没有警告，`default.pipe` 的 `let` 都用到了，执行完 `default.pipe` 后仍为 `none` 的变量（内部 pass 的开关除外）正好是 `rewrites`、`bit_split_budget`、`time_limit`，没有命令行时还有 `restarts`、`iter_limit`（都有测试检查）。

## 14. 例子

```
# 只在没有乘积时关掉 poly_mba（按输入形状选 pass）
(if (mul < 1) (off poly_mba))

# 从同一个起点做两种重建，取小的
(save t) | (best 1 rewrite ((load t) | (off clustered) | rewrite))

# 另一种重建，只在它确实不同且更小时作为候选
(save t) | (union id (cand halve_input (load t) | halve | (filter (!(same t) && size < (size t))) | rebuild))

# 先存默认值，条件满足时覆盖
(save b) | (if mixed (rewrite | (save b))) | (load b)

# 组变量存另一条管线的结果，当前候选组原样传下去
t = (lowbits | unshift) | rewrite | (filter (size < (size t)))

# 给一段步骤限时，到期后跳过它们，接着运行后面的
lowbits | time_limit = 500 | relate | tfunc | time_limit = none | finish

# 只在这一段里改限值，值按输入算
(split_runs = vars * 2 | split_bits) | rewrite

# 局部改写：每步只在变小时采用，至多采用 8 次
(scope rewrites = polish_rewrites
  | (wins 8
      (smaller polish/push_not polish/push_not)
      | (smaller polish/factor polish/factor)))
```

命令行上：

```bash
eggy1 --show-passes                                         # 入口程序（注释行）和当前的全部设置
eggy1 --passes "extra=0 off=relate" -n u32 "expr"
eggy1 --passes "prepass=lowbits | (if mixed rewrite)" -n u32 "expr"
eggy1 --passes "prepass=lowbits | relate=0 | rewrite time_limit=2000" -n u32 "expr"   # 前一项里的赋值，后一项是时限
eggy1 --passes "file=my.pipe" -n u32 "expr"
cargo run --release --example bench -- --passes "pre-=halve_input" bench-data/a.txt
python -I scripts/bench-shards.py ... "--passes=off=relate;extra=0"   # 写成一个参数
```
