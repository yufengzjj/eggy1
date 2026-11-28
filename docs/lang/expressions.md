# 表达式

## 1. 求值

- 表达式在执行到它的那一刻、对当时的输入（一个组或一个项）求值，结果是一个数或 `none`。
- `if` 的条件对输入求值；`retry` 的条件对 `a` 的结果求值；`filter`、`any`、`all` 对每个元素单独求值；`fix`、`wins` 的次数在进入形式时求值，`best` 的个数在各支运行之后求值。
- 作条件用时，非 0 为真（`none` 为真）。
- 作次数用时，`none` 是不限。

## 2. 运算

| 运算 | 规则 |
|---|---|
| `a + b`、`a * b` | 溢出或有一边是 `none` 时得 `none` |
| `a - b` | 饱和：小于 0 时得 0；`none - n` 是 `none`，`n - none` 是 0（`none - none` 也是 0） |
| `a / b` | 向下取整；`b` 为 0 时得 `none`（`none / 0` 也是）；`n / none` 是 0（`none / none` 也是），`none / n` 是 `none` |
| 比较 | 照常比较，`none` 大于所有整数，`none == none` |
| `!a` | `a` 为 0 时得 1，否则得 0 |
| `a && b`、`a \|\| b` | 得 1 或 0；从左到右，结果确定后不再求后面的操作数 |

这些运算是《[化简库的内置函数](../lang-lib/builtins.md)》 第 2 节说的运算符，签名在 `--show-builtins` 的 operators 一组里。

## 3. 数值函数

数值函数对当前输入现算，什么都不存。输入是 `term` 的数值函数要一个项：在组上写 `(size main)`、`(size (index i r))`，单独写 `size` 时报错（《[组、元素和管线](pipeline.md)》 第 2 节）；在逐个元素的条件里（`filter`、`any`、`all`）和 `main | ...` 之后它拿到的就是一个项。**组为空、项为 none 时，数值函数都得 0**。程序顶层在给出值的一步之前没有输入（不是空组），那里读输入的数值函数报错，单独写的和写了括号的一样（`size + 1`、`(moved)`、`(size main)` 报 `... has no input here ...`，《[函数](functions.md)》 第 8 节）；要在空组上求值就从一个空组开始：`empty = ((parse "x") | none)` 之后 `empty | (print (size main))` 写 0。（`none` 只表示变量没赋值，数值函数不会得 `none`。）

**形状**（一个项的数）：`size`（节点数）、`vars`、`depth`、`mul`（乘积数）、`bitconst`（与常数的位运算数）、`arith_in_bit`（位运算下的算术数）、`shift`、`div`。

**性质**（1 或 0；除另有说明外看一个项，在组上写 `(mixed main)` 等）：

| 名字 | 为 1 时 |
|---|---|
| `(opaque p)` | 有移位、除法或 `mulhi`，且预处理 `p` 的重建大于 `tiny_size` 个节点（会运行 `(prepass p)`；组上写 `(opaque p main)`） |
| `(rebuilds p)` | 预处理 `p` 会改变它（会运行 `(prepass p)`；组上写 `(rebuilds p main)`） |
| `minimal` | 组里某个元素被证明最小：没有更小的项与它相等（`prove_minimal` 开着时才证明） |
| `mixed` | 位运算下直接有算术或常数 |
| `moved` | 上一个 `fix` 停在次数上，第一个元素还在变 |
| `input` | 它就是本次运行的输入：`pipeline` 里是 `simplify` 的输入，`prepass` 里是预处理的那个项，`polish` 里是那个项；pass 在子项上运行的函数（`rewrite`、`simba_steps`……）里总是 0 |
| `tiny` | 至多 `tiny_size` 个节点 |
| `fits_split` | 至多 `split_size` 个节点 |
| `used_wide`、`used_clustered` | 组里有一个元素的 `used` 里有这一位（看整组） |
| `few_rewrites` | 它的 `rewrites` 至多 `unclustered_after` |
| `replaceable` | 整体有更小的 T-函数形式 |
| `abstracted` | 来源是抽象了子项的重建（`over_const_bitwise`、`over_shared_bitwise`） |
| `no_leaves` | 是没有叶子的线性区域 |
| `wide` | 是叶子多于 `max_leaves` 个的线性区域 |
| `const_bitwise` | 有与常数的位运算 |
| `cofactor` | 本次运行在重建 `poly_mba` 的线性余因子 |

性质之中，`opaque`、`rebuilds` 要跑一次预处理，比较贵；其余只看项本身或它的附带信息。

**带参数的函数**：
- `main` 是序言里的 `(def @inline (main g) (index 0 g))`：`(main R)` 是组变量 `R` 的第一个元素，单独写在要项的地方是这一步输入的第一个元素（`(size main)`），单独作一步时给出它（`a | main | prepass ...`）；`R` 为空或没绑定时是 none。`(index I R)` 是第 `I` 个（从 0 起）元素；`I` 为 `none` 或超出时是 none。
- `(size (main R))`：`R` 第一个元素的大小；none 时得 0。
- `(same r t)`：`t` 和 `r` 是同一个项时为 1（`(same (main R) main)`，在 `filter` 里 `(same (main R))`）；有一边为 none 时为 0。
- `(any C)`：有一个元素单独满足 `C`；`(all C)`：组不空，且每个元素都单独满足（`C` 是 `term->num`）。

比较照常比较这些 0：`(filter (size < (size (main r))))` 在 `r` 为空时什么也不留，`(filter (size > (size (main m))))` 在 `m` 为空时留下全部；空组上 `(0 < 1)` 照样为真。默认管线读的组变量在读时都不为空。

变量（《[化简库的变量](../lang-lib/variables.md)》）在表达式里读当前绑定的值：`(if rerun_input ...)`、`(fix (restarts - 1) later)`、`(filter (size <= split_size))`。

**以数结束的管线**：管线的最后一步可以是用到输入、给出数的步骤（数值函数、返回数的函数，可以带运算：`a | main | size > 3`），整条管线就给出一个数（《[组、元素和管线](pipeline.md)》 第 2 节）。在表达式里写在括号里，凡是要数的地方都能写：赋值右边 `x = (rewrite | main | size)`、表达式参数 `(fix (rewrite | main | size) p)`、比较和运算的一边 `((rewrite | main | size) < (size main))`、`def` 的数值参数、`filter`、`any`、`all` 的条件。括号里 `|` 之前的位置是一个数值函数或返回数的函数时，那仍是它的调用（`(f 3 a | b)` 是 `f` 的最后一个管线参数）；否则括号里有一个不在更深括号里的 `|` 时就是这种管线。

- 在当前输入上运行（以值开头的 `(t | rewrite | main | size)` 从那个值开始），各步是所在运行的步骤：读写所在运行的组变量和参数（`((t = rewrite | main | size) > 0)` 之后 `t` 可读），外面的 `smallest` 在它的计算步骤后面照样插 `note`，过了截止时刻各步照常跳过，最后的数在当时的输入上算。管线本身是一个作用域，里面的赋值不漏出来。
- 在 `filter`、`any`、`all` 里对每个元素单独运行。
- `--show-passes` 照写下的样子打印；`(minimal (lowbits | unshift))` 这样给数值函数显式写的管线输入打印成 `(lowbits | unshift | minimal)`，意思相同。
