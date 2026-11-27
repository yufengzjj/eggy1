# 管线语言参考

eggy1 的化简流程由几条管线描述，默认的写在 `src/default.pipe` 里，`--passes` 可以替换或改写它们，`--show-passes` 打印当前的全部设置。本文是这门语言的参考：数据模型、语法、形式、赋值、pass、条件、变量、`--passes` 的写法、静态检查。

一次运行执行一个**入口程序**：

```
<default.pipe 的赋值> | restarts = M | iter_limit = I | <--passes 的赋值> | pipeline
```

`default.pipe` 和 `--passes` 里的 `NAME=VALUE` 项、`off` 项（第 8 节）按出现的顺序成为赋值步骤，`-m M`、`-i I` 是其中的 `restarts = M`、`iter_limit = I`。它们在最外层运行的最外层作用域里执行，所以运行结束时全部撤销，下一次运行（下一个表达式）重新从头执行。从 Rust 直接进入别的管线时（测试和 `fuzz --prepass` 调用 `simplify_linear_with` 即 `prepass`、`polish`，不在任何运行里的 `rewrite`），前面接同一段赋值（没有 `-m`、`-i` 那两步），入口换成那条管线。已经在一次运行里时，嵌套的运行不再执行它们。

## 1. 数据模型

- 管线处理一组**候选**：彼此等价的项，第一个是**主候选**。每一步拿到一组候选，给出另一组，所以任何 pass 都能接在任何 pass 后面。
- 候选记着**来源**（origin，产生它的 pass 或 `cand` 名，`--stats` 按它计数）、哪些 pass 给过它被保留的形式（`used_wide`、`used_clustered`），以及产生它用了多少次未缓存的 `rewrite`（`few_rewrites`）。
- 一组候选可以是空的。空组照常往下传：大多数 pass 对空组什么也不做，条件在空组上为假。
- 每条管线的一次运行有自己的一套**寄存器**（`save`/`load`），运行之间、管线之间不共享。
- 超过时限（第 4.2 节的 `time_limit = N`；`--passes time_limit=MS` 是入口程序里的这一步，给整次运行设一个）后，干活的步骤原样返回输入，所以任何时候停下来结果都正确。只搬动候选的步骤照常执行：`seq` 本身、赋值（包括 `on`、`off`）、`save`、`load`、`label`、`filter`、`id`、`none`、`within`、`pre_done`，所以寄存器照常可用，清除时限后管线能接着往下走。时限只在步骤之间检查，打断不了正在运行的单个步骤（一轮 egglog、一次大的 `poly_mba` 展开）。

### 管线

| 名字 | 谁运行它 | 输入 | 说明 |
|---|---|---|---|
| `pipeline` | `simplify` | 输入表达式 | 整个化简：预处理、egglog 各轮、polish、从打印结果再跑一遍 |
| `prepass` | `prepass` pass、条件 `opaque`/`rebuilds` | 一个项 | 预处理：造出几个重建候选，按大小排好 |
| `polish` | `polish` pass | 每个候选单独 | 局部改写，只在变小时保留 |
| `rewrite` | 单项 pass 内部、`regions`、`again` | 一个项或子项 | 带缓存的重建，单项 pass 对子项也用它 |
| `simba` | `simba` 候选、`poly_mba` 的线性余因子 | 一个线性区域 | 线性区域的各种重建方法 |
| `sub/NAME` | 重建子项的单项 pass | 一个子项 | 见第 7 节 |

## 2. 词法

- 空白只用来分隔；`#` 到行尾是注释。
- **名字**以字母或 `_` 开头，可以含字母、数字、`_`、`/`：`polish/factor`、`semi/bit_split`、`split_runs`。所以 `/` 两边是名字时必须留空格：`x / 2`；`3/4` 是三个记号 `3` `/` `4`，只有在两边都是数时才不必留空格。`-` 不能出现在名字里，总是减号：`size-mul` 就是 `size - mul`，`restarts-1` 就是 `restarts - 1`。
- **数**是十进制非负整数。
- 其他记号：`( ) | = || && ! + - * / < <= > >= == !=`。`=` 是赋值（第 4.1 节），`==` 是比较；`=` 两边可以有空格，也可以没有。`--passes` 的各项（`extra=0`、`prepass=...`）是在语言之外分项的（第 8 节）。

## 3. 语法

```
pipe   := stage ('|' stage)*               # 依次执行
stage  := NAME                             # 不带参数的 pass，或 let 定义的名字
        | NAME '=' rhs                     # 赋值，第 4.1 节
        | '(' FORM arg* ')'                # 形式
        | '(' pipe ')'                     # 分组
rhs    := 'none' | value                   # value 读到 |、) 或结尾为止
cond   := NAME | NUM | '!' cond | '(' expr ')'
expr   := expr '||' expr | expr '&&' expr | '!' expr
        | value CMP value | NAME | NUM
        | '(' 'any' expr ')' | '(' 'all' expr ')' | '(' 'same' REG ')'
        | '(' expr ')'
value  := value ('+'|'-') value | value ('*'|'/') value
        | NUM | NAME | '(' 'size' REG ')' | '(' value ')'
count  := NUM | NAME | '(' value ')'
CMP    := '<' | '<=' | '>' | '>=' | '==' | '!='
```

- 优先级从低到高：`|`（管道）；条件里 `||`、`&&`、`!`、比较、`+ -`、`* /`。同级左结合。
- `(` 后面紧跟形式关键字（第 4 节）时是一个形式，否则是分组。关键字是保留字，不能用作 `let` 的名字，单独出现时报 `NAME needs parentheses`（`egglog` 除外，它也可以不带参数）。
- 形式里作为参数的管线如果含 `|`，要加括号：`(best 1 (a | b) c)`。
- 条件和数是两种不同的东西：条件位置写数的表达式、或把特征当布尔用（`(if mul ...)`），解析时报错。只有数字本身可以作条件：非 0 为真，与候选无关，空组上也一样（`(if 1 a b)` 总是运行 `a`）。条件或次数里写 `=`（`(if (size = 3) ...)`）报错：赋值是一个步骤，比较要写 `==`。

## 4. 形式

下表中 `p`、`a`、`b` 是管线，`C` 是条件，`N`、`K` 是次数（第 6 节），`R` 是寄存器名。

| 形式 | 含义 |
|---|---|
| `a \| b`、`(seq a b ...)` | 依次执行，前一步的候选交给后一步 |
| `(union a b ...)` | 每个都在同一组输入上运行，输出合并、去重 |
| `(best K a b ...)` | 同 `union`，再按大小排序，保留最小的 `K` 个（至少 1 个）。保留的候选来自某个 alternative 时，记它一次 `won` |
| `(first a b ...)` | 依次运行，返回第一个给出非空且与输入不同的结果；都没有就返回输入 |
| `(fix N p)` | 重复 `p` 至多 `N` 次，主候选不再变化时停。停在次数上（还在变）时，条件 `moved` 为真 |
| `(if C a)`、`(if C a b)` | 对输入求 `C`，真时运行 `a`，否则运行 `b`（省略时是 `id`） |
| `(retry C a b)` | 运行 `a`；`C` 对 `a` 的结果成立时，在原输入上运行 `b`，`b` 的主候选不比 `a` 的大时取 `b` |
| `(filter C)` | 对每个候选单独求 `C`，只保留成立的 |
| `(smallest p)` | 运行 `p`；`p` 里任何一步出现过比结果更小的候选时，把其中第一个最小的放到结果最前面 |
| `(smaller NAME p)` | 运行 `p`，主候选变小才采用，否则返回输入。采用时来源改为 `NAME`，记 `NAME/won` 和 `NAME/gain` |
| `(wins N p)` | 重复 `p`，直到其中的 `smaller` 不再采用结果，或一共采用了 `N` 次 |
| `(tag NAME p)` | 运行 `p`，记时间 `NAME/run`；主候选变了时记 `NAME/won/来源`，来源改为 `NAME` |
| `(cand NAME p)` | 一个预处理候选：`NAME` 是 `pre` 列表（第 8 节）里的名字且被关掉时给出空组；否则运行 `(bit_split_budget = cand_bit_splits \| p)`，结果来源改为 `NAME`，记 `pre/NAME/made` |
| `(scope p)` | `p` 里对同一个项的各 pass 共用一个运行上下文（缓存）。也是作用域（第 4.1 节）；变量沿用外面的值 |
| `(regions p)` | 对每个候选：如果它是一个线性区域，叶子先用 `rewrite` 重建，整体用 `p` 的主候选；否则对它的操作数用 `rewrite` |
| `(again p)` | 运行 `p`；主候选在"位运算的算术叶子"处有变化时，对它再做一次 `rewrite`，变小才保留 |
| `(save R)` | 把当前候选组存进寄存器 `R`，原样往下传 |
| `(load R)` | 把当前候选组换成寄存器 `R` 的内容（空寄存器给出空组）。可以反复读 |
| `(label R)` | 只做统计：每个候选记 `stats::label`，与寄存器 `R` 的主候选来源不同时记 `pre/来源/differs` 和 `pre/来源/gain`；`--trace` 时打印候选 |
| `(off NAME ...)` | `NAME = 0 \| ...` 的简写：关掉内部 pass 或开关（第 5.5 节），直到所在的 seq 结束，见第 4.1 节 |
| `(on NAME ...)` | `NAME = 1 \| ...` 的简写：重新打开内部 pass，或打开开关 |
| `(egglog LABEL)`、`egglog` | 一轮 egglog：所有候选合并进一个 e-graph，饱和，提取。调度重复 `iter_limit` 次，back-off 调度用当时的 `match_limit`、`ban_length`。统计计在 `egglog/LABEL` 下，默认用 `first`、`later`、`rerun_input` |

`(let NAME p)` 不是形式，而是 `--passes` 的一项（第 8 节）：之后写到 `NAME` 的地方展开成 `p`。定义体直接写成 `a | b` 时，展开后平铺进所在的 seq，和直接写出来一样；定义体整个包在括号里，写成 `(a | b)` 时，展开成一条嵌套的 seq，于是它里面的赋值只在这里面有效。

### 4.1 赋值与作用域

`NAME = VALUE` 是一个步骤：它在**当前作用域**里给变量 `NAME`（第 7 节）绑定一个值，原样传下候选，作用到所在作用域结束；同一作用域里再赋值就覆盖这个绑定。这期间调用的管线（`prepass`、`polish`、`rewrite`……）和新的 `scope` 也读到这个值（按调用链动态绑定）。

- 右边是第 6.3 节的数，一直读到 `|`、`)` 或结尾：`split_runs = vars * 2 | split_bits`。执行到这一步时对当时的候选求值，没有值时（空组、空寄存器、除以 0）为 0。
- 开关（内部 pass、`cut`、`rerun_input`、`prove_minimal`，第 5.5 节）的值也是数：0 是关，其他是开。`relate = 0` 关掉 `relate`，`cut = 1` 打开 `cut`。`(off A B)` 是 `A = 0 | B = 0` 的简写，`(on A B)` 是 `A = 1 | B = 1` 的简写，同一作用域里以后写的为准。
- `none` 只能单独写在右边，表示不限：预算（`rewrites = none`）、限值、时限（`time_limit = none`）都可以；开关不收 `none`。每个变量在赋值之前都是 `none`（开关为开）。
- 有上限的变量（第 7.3 节表里写了上限的，如 `max_leaves` 最多 6，因为真值表是 `u64`）赋更大的值或 `none` 时报错，报错信息写明上限；右边是数字时解析时就报，是表达式时执行到这一步时报（这次运行停下，返回这个错误，如 `max_leaves = 8: max_leaves is at most 6`）。
- 不能赋值的名字：特征、条件名，写了报错。其他变量（包括运行设置 `keep`、`extra`、`printed`、`match_limit`、`ban_length` 和 `restarts`、`iter_limit`）都能在任何地方赋值，下次读到时生效。
- 赋值属于只搬动候选的步骤：过了时限照常执行。

**作用域**有三种：seq（`a | b | ...` 形成的一条序列，包括括号里的 `( ... )`、`(seq ...)`），`scope`，以及每条管线的一次运行。其他形式（`if`、`fix`、`union`、`best`、`first`、`retry`……）都不是作用域：`(if C split_runs = 4)` 那一支只有一步，绑定落在 `if` 所在的 seq 里；`(if C (split_runs = 4 | x))` 那一支是一条 seq，绑定只在里面有效。`default.pipe` 的 `gates` 写成 `(if (mul < 1) (off poly_mba)) | ...`，平铺进 `prepass` 的顶层 seq，所以一直关到这次预处理结束。

普通变量以最内层的绑定为准。预算（`rewrites`、`bit_split_budget`）和时限是链上所有绑定都起作用：内层的预算不超过外层剩下的，用掉的次数退出时也从外层扣除；内层的时限不晚于外层。缓存的结果只在它读过的变量（预算和时限除外）都与当时相同的地方复用。

### 4.2 时限：`time_limit = N`

- 从这一步起，这条 seq 剩下的步骤共有 `N` 毫秒；到期后剩下干活的步骤都被跳过（计入 `time_limit/skipped`），这条 seq 很快结束，外面的步骤照常运行。
- `time_limit = none` 回到进入这条 seq 时的时限（外层设的仍然有效）。`time_limit = 0` 是 0 毫秒：从此刻起就已到期。
- 时限叠加：外层 seq、外层管线的时限同时有效，取最早到期的。内层不能把时限延长到外层之后。
- 在数里读 `time_limit`，得到剩下的毫秒数：`time_limit = time_limit / 2`。
- `--passes time_limit=MS` 是入口程序里的一步赋值，在最外层运行开始时执行：从那一刻起计时，`prepass`、`polish` 这些嵌套的运行只读到同一个截止时刻，不重新计时。`time_limit=none` 不设截止。
- 时限到期时开关 `cut` 开着，就算整次运行被截断：`eggy1` 打印提示，bench 把没解出的用例记作 `cut`。默认 `pipeline` 开头是 `cut = 1`，所以 `--passes time_limit=MS` 设的总时限到期时算截断。`cut` 会被内层继承，所以里面再设的时限到期也算；不想算的地方写 `cut = 0`。
- 截断后得到的结果不进缓存。

```
a | time_limit = 1000 | b | time_limit = none | c    # 只限 b
a | (time_limit = 1000 | b) | c                     # 同上
a | time_limit = 1000 | b | c                       # b、c 共用 1000 ms
a | (if big time_limit = 200) | b | c               # 输入大时 b、c 共用 200 ms
```

寄存器属于整条管线的一次运行，不受作用域限制。

## 5. Pass

### 5.1 列表 pass

对整组候选操作。组为空时，除 `none` 外都原样返回。

| pass | 含义 |
|---|---|
| `id` | 原样返回 |
| `none` | 给出空组 |
| `prepass` | 对主候选运行 `prepass` 管线，给出它的结果：第一个是主重建，其后是要一起并入 e-graph 的 |
| `polish` | 对每个候选单独运行 `polish` 管线，变小时替换 |
| `take_minimal` | 第一个被证明最小的候选（条件 `minimal`）；没有就原样返回 |
| `reprint` | 主候选打印成中缀再读回 |
| `within` | 当前的 `rewrites` 用完时给出空组，否则原样返回 |
| `pre_done` | 预处理的结尾：统计保留的候选，来源改为 `pre/来源`；主候选与输入是同一个项时，按寄存器 `t0` 里输入原来的写法给出 |

### 5.2 单项 pass

对每个候选单独运行，用结果替换它。没有结果或结果不变时保留原候选（alternative 除外）。

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

### 5.3 Alternative

也是单项 pass，但对候选整体运行。找不到形式时**不给出候选**（而不是保留原候选），给出的候选来源是自己的名字，所以 `best` 能记哪一个胜出。

| pass | 含义 |
|---|---|
| `simba` | 运行 `simba` 管线 |
| `small_blocks` | 按合取基里的块（≤ 3 个叶子）逐块重建 |
| `wide_blocks` | 宽区域的分块重建；被保留时置 `used_wide` |
| `poly_mba` | 多项式 MBA 的展开、约化和因式分解 |
| `drop_unused` | 把值不依赖的叶子置 0 后重建 |
| `clustered` | 按用到的叶子把项分组，各组分别重建；被保留时置 `used_clustered` |
| `peel`、`peel_clustered` | 剥掉一个项再重建其余部分 |
| `semi_linear` | 带常数掩码区域的逐位重建 |
| `rebuild_values` | 按区域在 {0,1}^n 上的取值重建 |
| `common_multiple` | 提出系数相近的公倍数 `c·(v_1 + ... + v_k)` |
| `related_leaves` | 加上叶子间零关系的小倍数后重建 |
| `one_wide_term` | 整个区域写成一个位运算项 |

### 5.4 Polish pass

写作 `polish/NAME`，单项 pass，用在 `polish` 管线里：`push_not`、`join_constants`、`join_linear`、`over_const_bitwise`、`over_shared_bitwise`、`over_products`、`recombine`、`shift_cases`、`decompose`、`factor`。`--passes` 的 `polish=a,b,...` 是这些名字的简写（第 8 节）。

### 5.5 内部 pass 名与开关

下列名字是开关变量：`relate = 0`（或 `(off relate)`）关掉它，`relate = 1`（或 `(on relate)`）重新打开；`--passes` 的 `off=` 也接受它们。关掉之后，它在一串步骤里时返回输入，作为 alternative 时不给出形式。它们大多同时也是 pass 名；`poly/masked`、`semi/*` 只是内部步骤：

`lowbits unshift tfunc_whole relate tfunc unify_operands recombine cut_products shifted_xor simplify_rebuilt cluster_regions simba small_blocks wide_blocks poly_mba poly/masked rebuild_values common_multiple related_leaves one_wide_term semi_linear drop_unused clustered peel peel_clustered semi/grouped semi/peel_grouped semi/shapes semi/pairs semi/peel_shapes semi/semi_split semi/scaled semi/bit_split semi/short_consts`

默认关掉的是 `semi/peel_shapes`。

另外有这些**开关**：

| 名字 | 默认 | 含义 |
|---|---|---|
| `cut` | 0 | 开着时，时限到期而跳过的步骤会把整次运行记为截断（第 4.2 节） |
| `rerun_input` | 1 | 默认 `pipeline` 的第一轮：结果是 `mixed` 时带上原输入重跑（`(retry (rerun_input && ...) ...)`） |
| `prove_minimal` | 1 | 尝试证明候选最小（条件 `minimal`、pass `take_minimal`）；0 时什么都不证明 |
| `relate_parts` | 1 | `relate` 对叶子多于 `relate_leaves` 的区域也按部分处理；不带 `clustered` 的重建里设成 0 |

这些默认值和 `semi/peel_shapes = 0` 都写在 `default.pipe` 开头，是入口程序的赋值。

## 6. 条件与数

### 6.1 条件名

除另有说明外看主候选。下面的条件名在空组上为假（`!` 照常取反）；"有候选"写作 `(any 1)`。条件里也可以写变量名（第 5.5 节的开关和第 7 节的变量）：值不为 0 时成立，`none` 也成立，与候选无关，空组上也一样：`(if rerun_input ...)`、`(if (printed && !input) ...)`、`(if !relate ...)`。

| 名字 | 成立时 |
|---|---|
| `opaque` | 有移位、除法或 `mulhi`，且它的重建大于 `tiny_size`（会运行 `prepass`） |
| `rebuilds` | 预处理会改变它（会运行 `prepass`） |
| `minimal` | 某个候选被证明最小：没有更小的项与它相等（`prove_minimal` 开着时才证明） |
| `mixed` | 位运算下直接有算术或常数 |
| `moved` | 上一个 `fix` 停在次数上，主候选还在变 |
| `input` | 它就是 `simplify` 的输入 |
| `tiny` | 至多 `tiny_size`（3）个节点 |
| `fits_split` | 至多 `split_size` 个节点 |
| `used_wide`、`used_clustered` | 产生某个候选的 pass 里，`wide_blocks`/`clustered` 给过被保留的形式（看整组） |
| `few_rewrites` | 产生它的 pass 至多做了 `unclustered_after` 次未缓存的 `rewrite` |
| `replaceable` | 整体有更小的 T-函数形式 |
| `abstracted` | 来自抽象了子项的重建（`over_const_bitwise`、`over_shared_bitwise`） |
| `no_leaves` | 是没有叶子的线性区域 |
| `wide` | 是叶子多于 6 个的线性区域 |
| `const_bitwise` | 有与常数的位运算 |
| `cofactor` | 本次运行在重建 `poly_mba` 的线性余因子 |

### 6.2 组合与比较

- `C && D`、`C || D`、`!C`、括号，任意嵌套。
- `(same R)`：主候选和寄存器 `R` 的主候选是同一个项（结构相同，不只是大小相同）。
- `(any C)`：有一个候选单独满足 `C`；`(all C)`：有候选，且每个都单独满足。
- 比较 `V CMP W`：两边有一边没有值（如空寄存器）时为假。

### 6.3 数

- **特征**（主候选的形状）：`size`（节点数）、`vars`、`depth`、`mul`（乘积数）、`bitconst`（与常数的位运算数）、`arith_in_bit`（位运算下的算术数）、`shift`、`div`。
- `(size R)`：寄存器 `R` 主候选的大小。
- **变量**：第 5.5 节的开关和第 7 节表里的任一名字，取当前的绑定（开关是 0 或 1），存的是什么就读到什么；只有 `time_limit` 取剩下的毫秒数，`keep` 至少读作 1。默认 `pipeline` 的第一轮单独写出，所以写 `(fix (restarts - 1) later)`、`(fix (printed - 1) later)`。
- 算术在非负整数上：`-` 小于 0 时取 0，`/` 向下取整，除以 0 没有值。`size <= (size f) * 3 / 4` 就是 `4·size ≤ 3·(size f)`，因为 `size` 是整数。
- `fix`、`best`、`wins` 的次数在进入形式时对当时的候选求值（`best` 在各支运行之后），没有值时为 0。

## 7. 变量

变量在管线里用 `NAME = VALUE` 赋值（第 4.1 节），在数和条件里读（第 6 节），在 `--passes` 里写成 `NAME=VALUE` 项（第 8 节）。开关见第 5.5 节。

### 7.1 运行设置

默认值写在 `default.pipe` 开头（入口程序的赋值）；`restarts`、`iter_limit` 来自命令行。没有赋值时是 `none`。

| 名字 | 默认 | 含义 |
|---|---|---|
| `restarts` | `-m`（2） | 总轮数；默认 `pipeline` 写 `(fix (restarts - 1) later)`，因为第一轮单独写出 |
| `iter_limit` | `-i`（10） | 每轮 egglog 重复调度几次 |
| `keep` | 2 | 预处理保留几个候选（至少读作 1） |
| `extra` | 2 | 预处理还在改变结果时，额外跑几轮 |
| `printed` | 2 | 从打印结果再跑几轮（0 不跑）；默认 `pipeline` 写 `(fix (printed - 1) later)` |
| `match_limit` | 64 | back-off 调度：一条规则每次运行最多匹配几次，超过就被禁用；下一轮 egglog 起生效 |
| `ban_length` | 3 | back-off 调度：被禁用的规则先停几次运行；下一轮 egglog 起生效 |

### 7.2 预算、时限和设置

| 名字 | 默认 | 含义 |
|---|---|---|
| `rewrites` | 不限 | 预算：剩下的未缓存 `rewrite` 调用次数，用完后 `rewrite` 原样返回；里面用掉的次数也从外层扣除 |
| `bit_split_budget` | 不限 | 预算：剩下的 `bit_split` 拆分对数；每个 `cand` 设成 `cand_bit_splits`，同 `rewrites` 也从外层扣除 |
| `time_limit` | 不限 | 时限，赋值时从此刻起计毫秒（第 4.2 节），`none` 不限。`--passes time_limit=MS` 是入口程序里的赋值；bench 用 `-t` 乘以它的 `--time-limit` 比例（默认 0.8，0 时传 `none`）设置，写在 `--passes` 里的 `time_limit=` 在它之后，所以优先 |
| `semi_leaves` | `max_leaves` | 半线性区域最多几个叶子才重建 |
| `relate_leaves` | `max_wide_leaves` | `relate` 只处理叶子不多于此的区域 |

### 7.3 限值

默认值写在 `default.pipe` 开头（入口程序的赋值），Rust 里只有名字和上限；`--passes` 的 `NAME=VALUE` 项排在它们之后，所以覆盖默认值。`default.pipe` 漏写的变量是 `none`，测试 `default_pipe_assigns_every_variable` 检查执行完入口赋值后仍是 `none` 的只有 `rewrites`、`bit_split_budget`、`time_limit`（和没有命令行时的 `restarts`、`iter_limit`）。

| 名字 | 默认 | 含义 |
|---|---|---|
| `unclustered_relate_leaves` | 10 | 不带 `clustered` 的重建里，`relate` 只处理这么多叶子以内的区域 |
| `unclustered_rewrites` | 256 | 不带 `clustered` 的重建最多调用 `rewrite` 的次数，超过就放弃 |
| `unclustered_after` | 1024 | 其他重建的 `rewrite` 次数不超过此值时，才尝试不带 `clustered` 的重建 |
| `unified_rewrites` | 128 | 统一操作数后重建的最多 `rewrite` 次数 |
| `related_rebuilds` | 8 | `related_leaves` 最多重建几种组合 |
| `related` | 4 | `relate` 每个区域最多试几个算术叶子 |
| `bit_splits` | 4 | `bit_split` 每个区域最多重建几种拆分 |
| `cand_bit_splits` | 8 | 每个预处理候选最多几对 `P op Q`（`cand` 把预算 `bit_split_budget` 设成它） |
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
| `tiny_size` | 3 | 不大于此的重建不再细找：条件 `tiny`，`opaque` 要求重建大于它 |
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

`decompose_max_vars`、`decompose_min_free_size`、`decompose_max_free_classes`、`decompose_fill_max_vars`、`decompose_xor_max_shared` 决定最短位运算式的搜索；线程级的真值表缓存按这五个值分开存，所以不同作用域里的不同值各建一份表。`memo_contexts` 只决定缓存留多少结果，不改变结果，所以不记入缓存读过的变量。
`wide_blocks_cache_size` 和 `memo_contexts` 一样只决定缓存留多少，不记入读过的变量；`wide_blocks` 的缓存键里有全部限值的哈希。带自由常数的位运算式按大小逐层建表，进程内共用；表里的式子与 `shapes_max_size` 无关，只是最大那一层的式子不当操作数，不存它们的真值表列表，所以值小时少建几层，值大时补上那一层的列表再接着建。
`tfunc` 的查找表进程内共用，按位宽、变量数和 `tfunc_max_vars`、`tfunc_max_size`、`tfunc_points` 分开建，所以不同作用域里的不同值各建一份，正常运行只建默认那一份；没用到的求值点上变量都是 0，值和第 0 个点相同，不改变查表的结果。`tfunc_max_carries`、`tfunc_max_states`、`tfunc_max_factor` 也决定 `lowbits` 在上下文里的证明，每次 `lowbits` 调用读一次。

### 7.4 `sub/NAME`

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

## 8. `--passes`

`--passes` 的值是若干**项**，依次作用在 `src/default.pipe` 之上（`default.pipe` 本身也是这样一串项）。项分两种：赋值项（`NAME=VALUE`、`off` 项）按出现的顺序排进入口程序，每次运行时执行（见开头）；其他的是定义，读到时生效。

### 8.1 分项

- `;` 总是分项。
- 括号外的空白：后面一段形如 `KEY=`、`KEY+=`、`KEY-=` 或以 `(let` 开头，且前一段不以 `|` 结尾时，开始新的一项，否则接在上一项后面。所以 `prepass=lowbits | rewrite extra=0` 是两项，管线里可以有空格；`prepass=a | split_runs=4 | b` 是一项，`split_runs=4` 是管线里的赋值。
- `#` 到行尾是注释。

### 8.2 项

| 项 | 含义 |
|---|---|
| `pipeline=P`、`prepass=P`、`polish=P`、`rewrite=P`、`simba=P`、`sub/NAME=P` | 替换这条管线 |
| `polish=a,b,...` | 全是 polish pass 名时：依次尝试这些 `polish/NAME`，变小才保留，有一个变小就重来，至多保留 `polish_wins` 次 |
| `(let NAME P)` | 定义名字，之后的项里写到 `NAME` 的地方展开为 `P`（`a | b` 平铺，`(a | b)` 嵌套，见第 4 节）。`default.pipe` 定义的名字（`first_round`、`later`、`gates`、`rebuild_main`……）也能用 |
| `file=PATH` | 在此处读入文件里的各项 |
| `pre=a,b`、`pre+=`、`pre-=` | 造哪些预处理候选：`unified no_wide split_bits halve_first over_products over_const_bitwise over_shared_bitwise halve_input unclustered` |
| `off=a,b`、`off+=a`、`off-=a` | 内部 pass 的赋值（第 5.5 节）：`off+=a,b` 是 `(off a b)`，`off-=a` 是 `(on a)`，`off=a,b` 先把所有内部 pass 打开（`(on ...)`），再关掉 `a`、`b`；`off=` 只是全部打开 |
| `schedule=...`、`schedule+=`、`schedule-=` | 每轮 egglog 的步骤，逗号分隔的 `run:RS`（back-off 调度）、`once:RS`、`sat:RS`（饱和），`RS` 是 `default-ruleset canonicalization constant-folding analysis identity-zero-element simplify` 之一 |
| `NAME=VALUE` | 入口程序里的赋值 `NAME = VALUE`：任一变量或开关（第 5.5、7 节），如 `extra=0`、`prove_minimal=0`、`split_runs=8`、`time_limit=2000`、`time_limit=none`。值同管线里的写法（第 4.1 节），可以是表达式，对输入求值：`split_runs=vars*2`；后面的项可以读前面赋的值：`keep=keep+1`。同一个变量写两次，后一次为准 |

注意名字是**在读到那一项时展开**的：重新定义 `gates` 不会改变已经读好的 `prepass`，要再写一次 `prepass=...`。

## 9. 检查与警告

读完 `--passes` 后检查，出错时拒绝整个设置：

- 名字：未知的 pass、条件、数、变量、`on`/`off` 名、`sub/NAME`、规则集，都报错并列出已知的名字。
- 赋值：给特征、条件名赋值（`minimal=` 提示运行设置叫 `prove_minimal`）；开关赋 `none`；`none` 不是单独写在右边；条件或次数里写 `=`（提示比较用 `==`）。
- 形式的参数：个数、种类（条件、数、管线）不对。
- 旧写法报错并提示新写法：单名写法 `save/t`、`off/NAME`、`egglog/LABEL`（提示括号写法）；`seq(a,b)` 语法；`(with KEY=VALUE ... p)`（提示 `(KEY = VALUE | ... | p)`，它的 `bit_splits` 是现在的 `bit_split_budget`）；`(time-limit N)`（提示 `time_limit = N`，不限写 `time_limit = none`）；条件名 `true`（提示 `1`，只在有候选时为真的写 `(any 1)`）；名字里的 `-`：解析出错时，如果写了 `a-b` 这样的词，提示它读作 `a - b`、名字用 `_`，`a_b` 是已知名字时提示写 `a_b`（`--passes tfunc-whole=0` 也一样）。
- `egglog`、`reprint` 只能出现在 `pipeline` 里：只有 `simplify` 的运行才有 e-graph。
- `prepass` 和 `polish` 不能经过别的管线回到自己。调用关系：`prepass` pass 和条件 `opaque`、`rebuilds` 调用 `prepass`；`polish` pass 调用 `polish`；单项 pass、`regions`、`again` 调用 `rewrite`、`simba`、`sub/NAME` 这一组（这一组内部本来就是递归的）。
- 寄存器的读（`load`、`label`、`size`、`same`）前面必须有可能先执行的同名 `save`。按执行顺序算：`if` 的两支都算，`retry` 的条件在 `a` 之后，`best` 的次数在各支之后；`fix`、`wins`、`regions` 的体会重复执行，体里任何地方的 `save` 对整个体都算。这条检查找的是写错名字和顺序，不保证运行时一定有值。

以下只给警告：`eggy1` 和 `bench` 的父进程打印到 stderr，`bench --one` 子进程不打印。

- `--passes` 里定义了却没用到的 `let`。
- 存了却从不读的寄存器。
- 死存储：同一层又 `save` 了一次，中间没读。写在 `if`、`cand`、`first` 的后几支、`retry` 的 `b` 或循环体里的 `save` 不和外面的比较，所以 `(save t) | (if c (save t))` 这种先存默认值再覆盖的写法不算。
- 赋值（包括 `(on NAME)`、`(off NAME)`）是所在 seq（或整条管线）的最后一步：什么也影响不到。
- 同一条 seq 里同一个变量连赋两次，中间没有读它，也没有别的步骤。

默认管线没有警告，`default.pipe` 的 `let` 都用到了（有测试检查）。

## 10. 例子

```
# 只在没有乘积时关掉 poly_mba（按输入形状选 pass）
(if (mul < 1) (off poly_mba))

# 从同一个起点做两种重建，取小的
(save t) | (best 1 rewrite ((load t) | (off clustered) | rewrite))

# 另一种重建，只在它确实不同且更小时作为候选
(save t) | (union id (cand halve_input (load t) | halve | (filter (!(same t) && size < (size t))) | rebuild))

# 先存默认值，条件满足时覆盖
(save b) | (if mixed (rewrite | (save b))) | (load b)

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
