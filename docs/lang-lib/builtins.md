# 化简库的内置函数

## 1. 交给 pass 的函数

Rust 代码不按名字调用语言里的管线：一个内置函数要运行的管线是它的**函数参数**（类型 `pipe`），调用处写出传哪个，例如 `(relate rewrite)`、`(prepass prepass_steps)`、`(simba simba_steps)`。参数名以 `sub` 开头的（`sub`、`sub_region`）是 pass 用来重建输入的**部分**（子项，或由子项重建出的形式）的函数；其余（`p`）作用在整个输入上。`default.pipe` 定义了这几个不带参数的函数，`--passes` 的 `NAME=P` 项是重新定义它们的简写（《[命令行和 --passes](../cli.md)》）：

| 函数 | 简写 | 谁用 | 说明 |
|---|---|---|---|
| `pipeline` | `pipeline=P` | `simplify` | 整个化简：预处理、egglog 各轮、polish、从打印结果再跑一遍 |
| `prepass_steps` | `prepass=P` | `(prepass prepass_steps)`、`(opaque prepass_steps main)`、`(rebuilds prepass_steps main)` | 预处理：造出一个项的几种重建，按大小排好 |
| `polish_steps` | `polish=P` | `(polish polish_steps)` | 局部改写，只在变小时保留 |
| `rewrite` | `rewrite=P` | 预处理的步骤，和几乎每个 pass 的 `sub` 参数 | 一个项的重建：`(memo rewrite ...)`，带缓存（第 4.2 节） |
| `simba_steps` | `simba=P` | `(simba simba_steps)`、`poly_mba` 的线性余因子、`peel` 剩下的部分 | 线性区域的各种重建方法（第 4.3 节） |

调用它们和调用别的 `def` 一样是一次**运行**（《[函数定义](../lang/functions.md)》 第 4 节）；`prepass` 对每个元素是一次单独的运行（带 `trace`，输入是那个项），`polish` 也是。pass 在 Rust 里调用一个函数参数时，它也是一次单独的运行；参数是单项内置函数的调用时（`(rebuild rewrite)`、函数体只是 `(memo ...)` 的 `rewrite`），直接运行它，不像一个步骤那样计入统计。

## 2. 内置函数的签名

内置函数的签名声明在 `src/builtins.pipe` 里（在 `default.pipe` 之前读入），函数体在 Rust 里实现；《[表达式](../lang/expressions.md)》 第 3 节，第 3、4 节的表是它们的说明，完整的签名以 `builtins.pipe` 为准：

```
(extern [@ATTR ...] (NAME PARAM:TYPE ... INPUT:TYPE) [RESULT])
```

- 类型（作结果还有 `text`：`show`）：`num`（一个数）、`term`（组的一个元素）、`term?`（一个项或 none：作返回类型，或返回数的函数声明成 `term?` 的参数和输入，写成 `(main g)`、`(index i g)`；组从不当作项，要一个组的元素就写 `main`、`index`）、`group`（一个有序集合，元素是项）、`name`（统计名、来源名或记录寄存器名）、`text`（一个字符串，写成字符串字面量）、`any`（只用来格式化的值，见 `print`；只能是最后一个参数 `x:any...`，不是多态），以及函数类型 `A->B`（`A->B->C` 是 `A->(B->C)`）。`pipe` 是 `group->group` 的简写：管线，原样传进去，在函数里运行；两种写法相同，打印成 `pipe`。`group` 写在参数里（不是最后一个）时是一个组变量，调用时写它的名字（`(label r:group g:group) group`）。`TYPE...` 是一个或多个，`TYPE?` 可以省略（`if` 的 `b:pipe?`、`egglog` 的 `label:name?`）。
- 作参数时，`num` 是调用时对输入求一次值的表达式（`best` 的个数、`fix` 和 `wins` 的次数）；`term->num` 是对每个元素单独求值的条件（`filter`、`any`、`all`）；`group->num` 是对一个组求值的条件（`if` 对输入，`retry` 对 `a` 的结果）。这两种函数类型的参数也写成表达式，就是以隐式输入为参数的函数（《[函数定义](../lang/functions.md)》 第 3 节的隐式输入），所以写法和 `num` 参数一样。内置函数的参数只用 `pipe`、`term->num`、`group->num` 这几种函数类型，其他函数类型的参数还不支持。
- 最后一个参数是**输入**（`term`、`term?`、`group`，`parse` 的是 `text`），调用少写它时由这一步的输入填入；也可以显式写出（《[函数定义](../lang/functions.md)》 第 3 节）。返回类型写在最后；不写返回类型的声明（`(extern (print x:any...))`、`(extern (assert c:num msg:text))`）没有输入也没有返回值，作一步时原样传下输入。
- 声明前紧挨着的一行注释是它的说明。
- 属性：`@timed`：过了截止时刻调用被跳过、原样返回输入（《[变量与作用域](../lang/variables.md)》 第 3 节），不带它的函数照常执行；`@uncounted`：只和 `@timed` 一起写，这次跳过不把运行记为截断，也不计入 `time_limit/skipped`（`note`）；`@switch`：单项 pass，有一个同名的开关变量（《[化简库的变量](variables.md)》 第 1 节）。
- **运算符**：《[表达式](../lang/expressions.md)》 第 2 节的 `+ - * / < <= > >= == != && || !` 也是内置函数，名字是这些符号的声明就是运算符：`(extern (+ a:num b:num) num)`、`(extern (! a:num) num)`。运算符没有输入，参数全部写出，不带属性，只在表达式里照《[表达式](../lang/expressions.md)》 第 2 节写成中缀（`!` 写在前面），不能按名字调用（`(+ 1 2)` 报错）。`&&`、`||` 声明成 `(extern (&& a:num b:group->num...) num)`：第一个操作数是数，后面的是以输入为参数的函数，由运算符决定调不调用——从左到右求值，结果一旦确定（`&&` 遇到 0、`||` 遇到非 0）就不再求后面的（短路）；其余运算符每个操作数都求值。
- `extern` 只能写在 `builtins.pipe` 里，写在 `--passes` 或管线里报错。宏 `let`、`on`、`off` 和赋值不是函数，没有声明（宏 `smallest` 有声明，参数照它读）。

调用方式由输入和返回类型按组和元素的规则（《[组、元素和管线](../lang/pipeline.md)》 第 2 节）得出，`--show-builtins` 按它分组：

| 输入 → 返回 | 调用方式 |
|---|---|
| `group → group` | 整组 |
| `term → term` | 对每个元素调用；结果不变时保留原元素（单项、polish pass、`polish`） |
| `term → term?` | 对每个元素调用；没有结果时去掉这个元素（alternative） |
| `term → group` | 对每个元素调用，结果组接起来（`prepass`、`reprint`） |
| `term → num`、`term? → num` | 对一个项求值；none 时得 0（`size`、`mixed` 等形状和性质）；组上报错 |
| `group → num` | 对整组求值；组为空时得 0（`any`、`all`、`minimal`、`used_wide`、`used_clustered`，以及不看元素的 `moved`、`cofactor`） |
| `group → term?` | 从整组里取一个元素，没有时为 none（`index`；序言里的 `main`） |
| `text → group` | 从文本读出组（`parse`） |
| `term? → text` | 对一个项给出文本；none 时是空文本（`show`） |
| 没有返回值 | 没有输入，作一步时原样传下输入（`print`、`assert`） |
| 运算符 | 没有输入，在所在表达式的输入上对操作数求值 |

声明成 `term` 或 `term?` 的参数和显式输入只收 `(main g)`、`(index i g)`、单独的 `main` 这种项，写一个组（组变量、括号里的管线）报 `size takes t:term?; r is a group — write (main r)`。

解析照签名读参数：`num`、`term->num`、`group->num` 参数是一个 `earg`（数值函数 `any`、`all` 的参数是整个表达式），`group`、`name` 参数是一个名字，`pipe...` 是一个或多个步骤，《[词法和语法](../lang/syntax.md)》 第 2 节末尾说的那种 `pipe` 参数读到 `)` 为止，其他 `pipe` 参数各是一个步骤。位置、参数个数和种类的检查都照签名做（《[检查与警告](../lang/errors.md)》），报错时附上签名。

解析后，每个内置函数的调用（包括 `best`、`fix`、`if` 这些带管线参数的函数、数值函数和运算符）都是“函数 + 参数”的一次应用，`def` 的调用也是同一种应用，应用的是那个 `def`；运行时按上表的调用方式交给它输入，再经 Rust 里的一张分派表（`lang::builtins::BUILTINS`，每个声明一项）调用它的实现，运算符的表项由求值直接算（不经函数指针，没有分配）。`seq` 解析成序列，`smallest` 是宏，它们在表里没有实现。测试检查每个声明都有调用方式相符的实现，每个实现都有声明。

解析结果（`lang::ast::Pipe`）只有这几种节点：应用（内置函数或 `def`；返回数的函数写出的输入跟在参数后面，`(size (main r))`；不带参数写在 `print` 里、又求不了值时是函数值）、字面量（数、名字、字符串）、变量的读（全局变量按下标，局部变量按名字并记下它存的是数、组还是函数值，参数按位置）、管线字面量（序列；最后一步返回数时整个序列返回数，`(lowbits | size)`：前面的步骤作为一个作用域在当前运行里跑完，再在它们的结果上求最后一步）、一种绑定 `x = e`（全局变量、局部数变量、组变量、函数变量都是它，种类在解析时由左边和右边的类型定，《[变量与作用域](../lang/variables.md)》 第 5、6 节）、宏展开（《[变量与作用域](../lang/variables.md)》 第 4 节；在调用处展开的 `@inline` 函数也是，如 `main`）和单独写成值的函数（`Pipe::FnValue`，《[函数定义](../lang/functions.md)》 第 8 节）。

## 3. 带参数的组函数

下表中 `p`、`a`、`b` 是管线，`C` 是条件（`if`、`retry` 的是 `group->num`，`filter` 的是 `term->num`），`N`、`K` 是次数（`num`），`R` 是组变量。参数里有管线的是高阶函数；`a | b` 是序列，不是函数，列在这里是为了对照 `(seq ...)`。

| 函数 | 含义 | 空组、顺序 |
|---|---|---|
| `a \| b`、`(seq a b ...)` | 依次执行，前一步的值交给后一步（《[组、元素和管线](../lang/pipeline.md)》 第 2 节）；是作用域。`(seq t)` 是括号里以值开头的管线，从 `t` 开始 | — |
| `(union a b ...)` | 每个都在同一组输入上运行，输出按分支顺序连起来，去重时留先出现的 | 某支给出空组时只是不贡献 |
| `(best K a b ...)` | 同 `union`，再按大小排序（同样大小时保持原来的先后），保留最小的 `K` 个，至少 1 个。保留的第一个元素来自某个 alternative 时，记它一次 `won` | — |
| `(first a b ...)` | 依次运行，返回第一个非空、且与输入不同的结果；都没有就返回输入。"不同"比较项和来源 | — |
| `(fix N p)` | 重复 `p` 至多 `N` 次，第一个元素不再变化时停；停在次数上（还在变）时 `moved` 为 1 | 输入和结果都空算不变 |
| `(if C a)`、`(if C a b)` | 对输入求 `C`，真时运行 `a`，否则运行 `b`（省略时是 `id`） | — |
| `(retry C a b)` | 运行 `a`；`C` 对 `a` 的结果成立时，在原输入上运行 `b`，`b` 的第一个元素不比 `a` 的大时取 `b` | `b` 给出空组时取 `a`；`a` 给出空组、`b` 不空时取 `b` |
| `(filter C)` | 对每个元素单独求 `C`，只保留成立的 | — |
| `(smallest p)` | 宏（《[变量与作用域](../lang/variables.md)》 第 4 节）：运行 `p`；`p` 的文字里计算的步骤给出过比结果的第一个元素严格更小的项时，把其中第一个最小的放到结果最前面（去重） | 结果为空时原样返回 |
| `(smaller NAME p)` | 运行 `p`，第一个元素严格变小才采用，否则返回输入。采用时来源改为 `NAME`，记 `NAME/won`、`NAME/gain` | 输入或结果为空时返回输入 |
| `(wins N p)` | 重复 `p`，直到其中的 `smaller` 这一遍没有采用结果，或一共采用了 `N` 次 | `N` 为 0 时不运行 `p`，原样返回 |
| `(tag NAME p)` | 运行 `p`，记时间 `NAME/run`；第一个元素变了时记 `NAME/won/来源`，来源改为 `NAME` | — |
| `(origin NAME p)` | 运行 `p`，结果的来源都改为 `NAME`，记时间 `pre/NAME/made` | — |
| `(scope p)` | `p` 里对同一个项的各 pass 共用一个运行上下文（缓存）；是作用域 | — |
| `(regions sub p)` | 对每个元素：如果它是一个线性区域，整体用 `p` 的第一个元素、其中的原子叶子用 `sub` 重建；否则对它的操作数用 `sub` | — |
| `(again sub p)` | 运行 `p`；第一个元素在"位运算的算术叶子"处有变化时，对它再做一次 `sub`，变小才保留 | — |
| `(save R)` | 《[变量与作用域](../lang/variables.md)》 第 5 节：即 `R = id`；读 `R` 就写 `R`（管线开头、括号里或管线参数里），没绑定时是空组 | — |
| `(clear R)` | 打开一个空的记录寄存器 `R`（《[变量与作用域](../lang/variables.md)》 第 5 节），原样返回 | — |
| `(note R)` | 当前组里第一个最小的元素比最新打开的 `R` 里的严格更小（或 `R` 是空的）时记进去，原样返回；过了截止时刻和其他计算的步骤一样跳过，但不算截断（`@uncounted`） | 空组、没有打开的 `R` 时什么也不记 |
| `(take_min R)` | 关上最新打开的 `R`：它的项比当前组的第一个元素严格更小时放到最前面（去重），否则原样返回 | 当前组为空时原样返回 |
| `(label R)` | 只做统计：每个元素记 `stats::label`，与组变量 `R` 的第一个元素来源不同时记 `pre/来源/differs`、`pre/来源/gain`；`--trace` 时打印它们 | — |
| `(assert C "MSG")` | 没有返回值（`(assert c:num msg:text)`）：对这一步的输入求一次 `C`，不是 0 时输入原样传下；是 0 时这次运行以错误 `MSG` 结束（运行时错误，和其他错误一样返回，不 panic）。不带 `@timed`，过了截止时刻照样检查 | — |
| `(print X ...)` | 没有返回值（`(print x:any...)`）：把各个值用空格隔开、换行结尾写到 stderr，输入原样传下。每个值：表达式照 `num` 参数在这一步的输入上求值，写成数（`none` 写 `none`）；字符串原样；组变量写成各元素的中缀，用 `, ` 隔开（常数照最后输出的写法，按这次运行的数值类型）；单独写的函数名照《[函数](../lang/functions.md)》 第 8 节的规则：只少输入、这一步又有输入时求值，写成数或组的各元素（`(print rewrite)`）；否则（程序顶层开头没有输入、还少别的参数）是函数值，写它的签名（`(rewrite t:term) term`、`(size t:term?) num`，内置函数、`def`、`let` 一样；函数变量写 `f:term->num`）；其他名字照写。不带 `@timed`，过了截止时刻照样打印 | — |
| `(egglog LABEL)`、`egglog` | 一轮 egglog：组里所有元素并入一个 e-graph，饱和，提取出一个项。统计计在 `egglog/LABEL` 下 | — |

`tag`、`label`、`smaller`、`origin` 记的统计不影响结果；它们改的来源会影响结果（《[组、元素和管线](../lang/pipeline.md)》 第 1.2 节）。统计键里的名字就是语言里的名字（`polish_factor/run`、`final/polish_factor`、`pass/semi_shapes`），只有复合的键用 `/` 分隔各部分（`pre/NAME/made`、`NAME/won/ORIGIN`）。

**`cand`** 不是内置函数，是 `default.pipe` 里的 `@inline @timed` 函数：

```
(def @inline @timed (cand enabled:num n p) (if enabled (origin n (bit_split_budget = cand_bit_splits | p)) none))
```

`(cand pre_unified unified p)` 是预处理的一种重建：开关 `pre_unified` 为 0 时给出空组，否则在 `bit_split_budget = cand_bit_splits` 下运行 `p`（括号里的序列是作用域，预算到此为止），来源都改为 `unified`，记 `pre/unified/made`。开关作为数值参数显式写出，因为语言里不能由名字参数 `n` 拼出变量名 `pre_n`；没有开关的写 `(cand 1 first p)`。

## 4. 组函数（pass）

这些函数习惯上叫 pass。按调用方式分四种：整组、单项、alternative、polish（第 2 节，由签名决定）。参数是它要运行的函数（第 1 节）：`sub` 用来重建输入的部分，默认传 `rewrite`（`over_*`、`split_bits`、`shift_cases` 传 `(rebuild rewrite)`）；不带参数的写成名字。

### 4.1 整组

调用方式见各自的签名：`prepass`、`reprint`、`polish` 对每个元素调用（`prepass`、`reprint` 的结果组接起来；只对第一个元素做时写 `main | (prepass p)`），其余对整组。组为空时，除 `none` 外都原样返回。

| pass | 含义 |
|---|---|
| `id` | 原样返回 |
| `none` | 给出空组 |
| `(prepass p)` | 对每个元素运行预处理 `p`（每次是一次单独的运行），给出它的结果：第一个是主重建，其后是要一起并入 e-graph 的，来源是 `pre/来源`；同一个线程上最近一次的结果留着（`opaque`、`rebuilds` 和随后的这一步常对同一个项问） |
| `(polish p)` | 对每个元素单独运行 `p`（每次是一次单独的运行），结果的第一个元素变小时替换 |
| `take_minimal` | 第一个被证明最小的元素（`minimal`）；没有就原样返回 |
| `reprint` | 每个元素打印成中缀再读回 |
| `within` | 当前的 `rewrites` 用完时给出空组，否则原样返回 |
| `pre_done` | 预处理的结尾：统计保留的元素，来源改为 `pre/来源`；第一个元素与输入相同时，按组变量 `t0` 里输入原来的写法给出 |

### 4.2 单项

对每个元素单独运行，用结果替换它；没有结果或结果不变时保留原元素（alternative 除外）。

| pass | 含义 |
|---|---|
| `lowbits` | 已知位推理：只碰已知位的位运算改成加法、低位截断、按求值确定的低位 |
| `unshift` | 把 `c·(a >> s)` 等写成掩码形式，使区域成为半线性的 |
| `tfunc_whole` | 整个项换成更小的 T-函数形式（≤ `tfunc_max_vars` 个变量）；不适用时没有结果 |
| `tfunc` | 对子项做同样的替换 |
| `(memo n p)` | 在 `p` 上运行这个项，结果按项、`p`（哪个定义或哪处写的函数，第 1 节）和读到的变量缓存在 `scope` 里，每算一个新结果用掉一次 `rewrites`；统计计在 `pass/n` 下（`rewrite` 的函数体是 `(memo rewrite ...)`） |
| `(rewrite_top p)` | 运行 `p`，统计计在 `rewrite_top` 下 |
| `(cluster_regions sub)`、`(cluster_top sub)` | 对结果的每个区域做 `clustered` 式的分组重建；`cluster_top` 只是统计名不同 |
| `(relate sub)` | 把位运算的算术叶子换成占位变量，加上它们之间的零关系再用 `sub` 重建（相等的证明也用 `sub`：差重建成 0）；结果按项和 `sub` 缓存 |
| `unify_operands` | 统一位运算操作数的写法，让更多叶子能共享 |
| `(recombine sub)` | 把 `c·P1·Q1 + c·P2·Q2` 合回一个乘积（还原 `a·b` 的拆分），证明和因子的重建用 `sub` |
| `(cut_products sub)` | 按另一个因子的尾零截断乘积因子里的常数，截断后的因子用 `sub` 重建比较 |
| `shifted_xor` | `2^k·(a ^ K) + c` 写成 `(2^k·a) ^ (2^k·K + c)` |
| `simplify_rebuilt` | 只用于重建结果的 `lowbits` 部分（截断乘数等） |
| `(finish sub)` | 重建结果的收尾：`recombine`、`cut_products`（都用 `sub`）、`shifted_xor`，再 `lowbits` |
| `(halve sub)` | `2^k·a + c` 形式的操作数拆半：`2^k·(a op b) + (c op d)`，操作数用 `sub` 重建 |
| `(over_const_bitwise sub)`、`(over_shared_bitwise sub)` | 把与常数的位运算、或共享的位运算子项抽象成变量，用 `sub` 重建，再代回 |
| `(over_products sub)` | 把乘积抽象成变量，用 `sub` 重建，再代回 |
| `(split_bits sub)` | 按单个变量位分情况用 `sub` 重建，还原 Hikari/OLLVM 式的选择 |
| `drop_identities` | 去掉加 0、乘 1 |
| `(rebuild sub)` | 不带 `relate` 的一次重建：`lowbits`、`unshift`、`sub`、用 `sub` 的 `cluster_regions`、`tfunc` |

### 4.3 Alternative

也是单项函数，但对项整体运行。找不到形式时**给出 none**（这个元素被去掉，而不是保留原元素）；给出的项来源是自己的名字，所以 `best` 能记哪一个胜出。

| pass | 含义 |
|---|---|
| `(simba p)` | 在线性区域上运行 `p`（默认 `simba_steps`） |
| `small_blocks` | 按合取基里的块（≤ 3 个叶子）逐块重建 |
| `wide_blocks` | 宽区域的分块重建；被保留时置 `used` 的 wide 位 |
| `(poly_mba sub sub_region)` | 多项式 MBA 的展开（叶子和带常数位运算的因子用 `sub` 重建）、约化和因式分解，线性余因子用 `sub_region` 重建（按项和 `sub_region` 缓存） |
| `(drop_unused sub)` | 把值不依赖的叶子置 0 后用 `sub` 重建 |
| `(clustered sub)` | 按用到的叶子把项分组，各组用 `sub` 分别重建；被保留时置 `used` 的 clustered 位 |
| `(peel sub_region)`、`(peel_clustered sub_region)` | 剥掉一个项，其余部分用 `sub_region` 重建 |
| `(semi_linear sub)` | 带常数掩码区域的逐位重建，`bit_split` 的两边用 `sub` 重建 |
| `rebuild_values` | 按区域在 {0,1}^n 上的取值重建 |
| `common_multiple` | 提出系数相近的公倍数 `c·(v_1 + ... + v_k)` |
| `related_leaves` | 加上叶子间零关系的小倍数后重建 |
| `one_wide_term` | 整个区域写成一个位运算项 |

### 4.4 Polish

写作 `polish_NAME`，单项函数，用在 `polish_steps` 函数里：`push_not`、`join_constants`、`join_linear`、`over_const_bitwise`、`over_shared_bitwise`、`over_products`、`recombine`、`shift_cases`、`decompose`、`factor`。`join_constants`、`join_linear`、`recombine` 带 `sub`（默认 `rewrite`），`over_*`、`shift_cases` 带 `sub`（默认 `(rebuild rewrite)`，`shift_cases` 也用它证明各情况相等）。`--passes` 的 `polish=a,b,...` 是这些名字的简写（《[命令行和 --passes](../cli.md)》）。

## 5. 重建子项的函数

pass 重建子项（或由子项得到的形式）时运行它的 `sub` 参数（第 1 节），`default.pipe` 里写出传哪个：

| 传 `rewrite` | 传 `(rebuild rewrite)` |
|---|---|
| `clustered`、`cluster_regions` 的每一组；`relate`；`semi_linear` 里 `bit_split` 的两边；`halve` 的操作数；`drop_unused`；`recombine`、`finish`、`cut_products`；`poly_mba` 的叶子；`regions`、`again`；`polish_join_constants`、`polish_join_linear`、`polish_recombine` | `over_products`、`split_bits`、`over_const_bitwise`、`over_shared_bitwise`（预处理和 polish 的）、`polish_shift_cases` |

换掉某处的函数就在那个调用里写别的：`(def (by_parts) rewrite | tfunc) simba=... (clustered by_parts) ...`。命令行没有 `sub_NAME=P` 这样的项（报 `no longer read`）。

## 6. 例子

```
# 只在没有乘积时关掉 poly_mba（按输入形状选 pass）
(if ((mul main) < 1) (off poly_mba))

# 从同一个起点做两种重建，取小的
(save t) | (best 1 rewrite (t | (off clustered) | rewrite))

# 另一种重建，只在它确实不同且更小时加进组里
(save t) | (union id (cand pre_halve_input halve_input t | (halve rewrite) | (filter (!(same (main t)) && size < (size (main t)))) | (rebuild rewrite)))

# 先存默认值，条件满足时覆盖
(save b) | (if (mixed main) (rewrite | (save b))) | (b | id)

# 组变量存另一条管线的结果，输入原样传下去
t = (lowbits | unshift) | rewrite | (filter (size < (size (main t))))

# 给一段步骤限时，到期后跳过它们，接着运行后面的
lowbits | time_limit = 500 | (relate rewrite) | tfunc | time_limit = none | (finish rewrite)

# 只在这一段里改限值，值按输入算
(split_runs = (vars main) * 2 | (split_bits (rebuild rewrite))) | rewrite

# 局部改写：每步只在变小时采用，至多采用 8 次
(scope rewrites = polish_rewrites
  | (wins 8
      (smaller polish_push_not polish_push_not)
      | (smaller polish_factor polish_factor)))
```

命令行上：

```bash
eggy1 --show-passes                                         # 命令行写的程序（注释行）和当前的全部设置
eggy1 --passes "extra=0 off=relate" -n u32 "expr"
eggy1 --passes "prepass=lowbits | (if (mixed main) rewrite)" -n u32 "expr"
eggy1 --passes "prepass=lowbits | relate=0 | rewrite time_limit=2000" -n u32 "expr"   # 前一项里的赋值，后一项是时限
eggy1 --passes "file=my.pipe" -n u32 "expr"
cargo run --release --example bench -- --passes "pre-=halve_input" bench-data/a.txt
python -I scripts/bench-shards.py ... "--passes=off=relate;extra=0"   # 写成一个参数
```
