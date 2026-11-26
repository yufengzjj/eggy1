# 管线语言参考

eggy1 的化简流程由几条管线描述，默认的写在 `src/default.pipe` 里，`--passes` 可以替换或改写它们，`--show-passes` 打印当前的全部设置。本文是这门语言的参考：数据模型、语法、形式、pass、条件、设置、`--passes` 的写法、静态检查。

## 1. 数据模型

- 管线处理一组**候选**：彼此等价的项，第一个是**主候选**。每一步拿到一组候选，给出另一组，所以任何 pass 都能接在任何 pass 后面。
- 候选记着**来源**（origin，产生它的 pass 或 `cand` 名，`--stats` 按它计数）、哪些 pass 给过它被保留的形式（`used_wide`、`used_clustered`），以及产生它用了多少次未缓存的 `rewrite`（`few_rewrites`）。
- 一组候选可以是空的。空组照常往下传：大多数 pass 对空组什么也不做，条件在空组上为假。
- 每条管线的一次运行有自己的一套**寄存器**（`save`/`load`），运行之间、管线之间不共享。
- 超过时限（第 4.1 节的 `(time-limit N)`；默认 `pipeline` 开头用 `time_limit` 设一个，见第 7.2 节）后，干活的步骤原样返回输入，所以任何时候停下来结果都正确。只搬动候选的步骤照常执行：`seq` 本身、`save`、`load`、`label`、`filter`、`off`、`time-limit`、`id`、`none`、`within`、`pre_done`，所以寄存器照常可用，清除时限后管线能接着往下走。时限只在步骤之间检查，打断不了正在运行的单个步骤（一轮 egglog、一次大的 `poly_mba` 展开）。

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
- **名字**以字母或 `_` 开头，可以含字母、数字、`_`、`/`，以及后面紧跟字母或 `_` 的 `-`：`polish/factor`、`semi/bit_split`、`time-limit`。所以 `/` 两边是名字时必须留空格：`x / 2`；`3/4` 是三个记号 `3` `/` `4`，只有在两边都是数时才不必留空格。`-` 后面是数时是减号（`restarts-1`），后面是名字时要留空格（`size - mul`，`size-mul` 是一个名字，报未知名字）。
- **数**是十进制非负整数。
- 其他记号：`( ) | || && ! + - * / < <= > >= == !=`。
- **设置** `KEY=VALUE`：一个名字紧跟 `=`（不是 `==`），再紧跟一个值，中间都不能有空格；值一直读到空白或括号为止。它只用在 `with` 里，`KEY` 和 `VALUE` 见第 7.1 节。语言里没有别的赋值：开关写成 `(on NAME)`、`(off NAME)`，寄存器写成 `(save R)`。`--passes` 的各项（`extra=0`、`prepass=...`）是在语言之外分项的（第 8 节），不是这里的设置。

## 3. 语法

```
pipe   := stage ('|' stage)*               # 依次执行
stage  := NAME                             # 不带参数的 pass，或 let 定义的名字
        | '(' FORM arg* ')'                # 形式
        | '(' 'with' SETTING+ pipe ')'     # 设置，第 7.1 节
        | '(' pipe ')'                     # 分组
SETTING := KEY '=' VALUE                   # 中间无空格
cond   := NAME | '!' cond | '(' expr ')'
expr   := expr '||' expr | expr '&&' expr | '!' expr
        | value CMP value | NAME
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
- 条件和数是两种不同的东西：条件位置写数、或把特征当布尔用（`(if mul ...)`），解析时报错。

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
| `(cand NAME p)` | 一个预处理候选：`NAME` 是 `pre` 列表（第 8 节）里的名字且被关掉时给出空组；否则运行 `p`（如同 `(with bit_splits=bit_split_budget p)`），结果来源改为 `NAME`，记 `pre/NAME/made` |
| `(scope p)` | `p` 里对同一个项的各 pass 共用一个运行上下文（缓存）。也是作用域（第 4.1 节）；设置、开关、时限沿用外面的值 |
| `(with KEY=V ... p)` | 第 7.1 节的设置，`p` 结束后恢复；写在哪里都有效。也是作用域，所以要在里面关掉 pass 就写 `(with rewrites=8 (off relate) \| p)` |
| `(regions p)` | 对每个候选：如果它是一个线性区域，叶子先用 `rewrite` 重建，整体用 `p` 的主候选；否则对它的操作数用 `rewrite` |
| `(again p)` | 运行 `p`；主候选在"位运算的算术叶子"处有变化时，对它再做一次 `rewrite`，变小才保留 |
| `(save R)` | 把当前候选组存进寄存器 `R`，原样往下传 |
| `(load R)` | 把当前候选组换成寄存器 `R` 的内容（空寄存器给出空组）。可以反复读 |
| `(label R)` | 只做统计：每个候选记 `stats::label`，与寄存器 `R` 的主候选来源不同时记 `pre/来源/differs` 和 `pre/来源/gain`；`--trace` 时打印候选 |
| `(off NAME ...)` | 从这里起，关掉内部 pass 或开关（第 5.5 节），直到所在的 seq 结束，见第 4.1 节；这期间调用的管线（`prepass`、`polish`、`rewrite`……）也继承这一设置 |
| `(on NAME ...)` | 同上，方向相反：重新打开内部 pass，或打开开关。同一作用域里 `on` 和 `off` 以后写的为准 |
| `(egglog LABEL)`、`egglog` | 一轮 egglog：所有候选合并进一个 e-graph，饱和，提取。统计计在 `egglog/LABEL` 下，默认用 `first`、`later`、`rerun_input` |
| `(time-limit N)` | 从这里起，所在的 seq 剩下的部分有 `N` 毫秒，见第 4.1 节；`N` 为 0 时清除 |

`(let NAME p)` 不是形式，而是 `--passes` 的一项（第 8 节）：之后写到 `NAME` 的地方展开成 `p`。定义体直接写成 `a | b` 时，展开后平铺进所在的 seq，和直接写出来一样；定义体整个包在括号里，写成 `(a | b)` 时，展开成一条嵌套的 seq，于是它里面的 `(time-limit N)`、`(off NAME)` 只在这里面有效。

### 4.1 作用域：`(time-limit N)`、`(on NAME)`、`(off NAME)`

**作用域**有四种：seq（`a | b | ...` 形成的一条序列，包括括号里的 `( ... )`、`(seq ...)`），`with`，`scope`，以及每条管线的一次运行。其他形式（`if`、`fix`、`union`、`best`、`first`、`retry`……）都不是作用域。`(time-limit N)`、`(on NAME)`、`(off NAME)` 都从写下的位置起，作用到它所在的最内层 seq 结束；这期间调用的管线（`prepass`、`polish`、`rewrite`……）也受它们影响。`on`/`off` 就是这样；`(time-limit N)` 的细节如下：

- 从这一步起，这条 seq 剩下的步骤共有 `N` 毫秒；到期后剩下干活的步骤都被跳过（计入 `time-limit/skipped`），这条 seq 很快结束，外面的步骤照常运行。
- `(time-limit 0)` 清除本 seq 里设的时限，回到进入这条 seq 时的时限（外层设的仍然有效）。
- seq 结束时，它里面设的时限随之失效。
- 时限叠加：外层 seq、外层管线的时限同时有效，取最早到期的。内层不能把时限延长到外层之后。
- `N` 是第 6.3 节的数，进入这一步时求值，可以读特征和限值：`(time-limit (size * 10))`。
- 时限到期时开关 `cut` 开着，就算整次运行被截断：`eggy1` 打印提示，bench 把没解出的用例记作 `cut`。默认 `pipeline` 开头是 `(time-limit time_limit) | (on cut)`，所以 `--passes time_limit=MS` 设的总时限到期时算截断。`cut` 会被内层继承，所以里面再设的时限到期也算；不想算的地方写 `(off cut)`。
- 截断后得到的结果不进缓存。

不是 seq 的形式参数（`with`、`scope` 的除外）不形成作用域：`(if C (time-limit 100))` 那一支只有一个 pass，时限作用到 `if` 所在的 seq；`(if C ((time-limit 100) | x))` 那一支是一条 seq，时限只限 `x`。`(off NAME)` 同理：`default.pipe` 的 `gates` 写成 `(if (mul < 1) (off poly_mba)) | ...`，平铺进 `prepass` 的顶层 seq，所以一直关到这次预处理结束。

```
a | (time-limit 1000) | b | (time-limit 0) | c    # 只限 b
a | ((time-limit 1000) | b) | c                  # 同上
a | (time-limit 1000) | b | c                    # b、c 共用 1000 ms
a | (if big (time-limit 200)) | b | c            # 输入大时 b、c 共用 200 ms
```

`with` 的设置和 `scope` 的运行上下文只在包住的管线里有效，也包括其间调用的管线；寄存器属于整条管线的一次运行，不受作用域限制。

设置（第 7.1 节）、开关、限值（第 7.2 节）和时限都是线程上的变量，按调用链动态绑定：`with`、`(on NAME)`、`(off NAME)`、`(time-limit N)` 在当前作用域里绑定，作用域结束时恢复外面的值；调用的管线和新的 `scope` 都读到调用处的值。普通变量以最内层的绑定为准。预算（`rewrites`、`bit_splits`）和时限是链上所有绑定都起作用：内层的预算不超过外层剩下的，用掉的次数退出时也从外层扣除；内层的时限不晚于外层。缓存的结果只在它读过的变量（预算和时限除外）都与当时相同的地方复用。

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
| `within` | 外层 `with` 的 `rewrites` 用完时给出空组，否则原样返回 |
| `pre_done` | 预处理的结尾：统计保留的候选，来源改为 `pre/来源`；主候选与输入是同一个项时，按寄存器 `t0` 里输入原来的写法给出 |

### 5.2 单项 pass

对每个候选单独运行，用结果替换它。没有结果或结果不变时保留原候选（alternative 除外）。

| pass | 含义 |
|---|---|
| `lowbits` | 已知位推理：只碰已知位的位运算改成加法、低位截断、按求值确定的低位 |
| `unshift` | 把 `c·(a >> s)` 等写成掩码形式，使区域成为半线性的 |
| `tfunc_whole` | 整个项换成更小的 T-函数形式（≤ 3 个变量）；不适用时没有结果 |
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

### 5.5 内部 pass 名与开关（`off`、`on`）

`(off ...)`、`(on ...)` 和 `--passes` 的 `off=` 接受下列名字。关掉之后，它在一串步骤里时返回输入，作为 alternative 时不给出形式。它们大多同时也是 pass 名；`poly/masked`、`semi/*` 只是内部步骤：

`lowbits unshift tfunc_whole relate tfunc unify_operands recombine cut_products shifted_xor simplify_rebuilt cluster_regions simba small_blocks wide_blocks poly_mba poly/masked rebuild_values common_multiple related_leaves one_wide_term semi_linear drop_unused clustered peel peel_clustered semi/grouped semi/peel_grouped semi/shapes semi/pairs semi/peel_shapes semi/semi_split semi/scaled semi/bit_split semi/short_consts`

默认关掉的是 `semi/peel_shapes`。

`(on ...)`、`(off ...)` 另外接受**开关**，开关默认是关的：

- `cut`：开着时，时限到期而跳过的步骤会把整次运行记为截断（第 4.1 节）。

## 6. 条件与数

### 6.1 条件名

除另有说明外看主候选。所有条件在空组上为假（`!` 照常取反）。

| 名字 | 成立时 |
|---|---|
| `true` | 总是（有候选时） |
| `opaque` | 有移位、除法或 `mulhi`，且它的重建不是很小（会运行 `prepass`） |
| `rebuilds` | 预处理会改变它（会运行 `prepass`） |
| `minimal` | 某个候选被证明最小：没有更小的项与它相等 |
| `mixed` | 位运算下直接有算术或常数 |
| `moved` | 上一个 `fix` 停在次数上，主候选还在变 |
| `input` | 它就是 `simplify` 的输入 |
| `rerun_input` | 设置 `rerun_input` 开着 |
| `printed` | 设置 `printed` 不为 0 |
| `tiny` | 至多 3 个节点 |
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
- **计数**：`restarts`（`-m` 减去第一轮）、`extra`、`printed`（减去第一轮）、`keep`，即第 8 节的同名设置。
- **限值**：第 7 节表里的任一名字，取当前值。
- 算术在非负整数上：`-` 小于 0 时取 0，`/` 向下取整，除以 0 没有值。`size <= (size f) * 3 / 4` 就是 `4·size ≤ 3·(size f)`，因为 `size` 是整数。
- `fix`、`best`、`wins` 的次数在进入形式时对当时的候选求值（`best` 在各支运行之后），没有值时为 0。

## 7. 设置与限值

### 7.1 `with` 的设置

| 键 | 默认 | 含义 |
|---|---|---|
| `rewrites` | 不限 | 剩下的未缓存 `rewrite` 调用次数，用完后 `rewrite` 原样返回；里面用掉的次数也从外层扣除 |
| `semi_leaves` | 6 | 半线性区域最多几个叶子才重建 |
| `relate_leaves` | 16 | `relate` 只处理叶子不多于此的区域 |
| `bit_splits` | 不限 | 剩下的 `bit_split` 次数；每个 `cand` 从 `bit_split_budget` 开始，同 `rewrites` 也从外层扣除 |

写作 `KEY=VALUE`，中间无空格；一个 `with` 可以有多个设置，至少一个。值是数，或限值的名字（`(with rewrites=polish_rewrites p)`）。没有 `off=`：在 `with` 里写 `off=X` 会报错，并提示改成 `(with ... (off X) | p)`。

### 7.2 限值

用 `--passes` 的 `NAME=数` 设置，也可以在条件和次数里读。

| 名字 | 默认 | 含义 |
|---|---|---|
| `unclustered_relate_leaves` | 10 | 不带 `clustered` 的重建里，`relate` 只处理这么多叶子以内的区域 |
| `unclustered_rewrites` | 256 | 不带 `clustered` 的重建最多调用 `rewrite` 的次数，超过就放弃 |
| `unclustered_after` | 1024 | 其他重建的 `rewrite` 次数不超过此值时，才尝试不带 `clustered` 的重建 |
| `unified_rewrites` | 128 | 统一操作数后重建的最多 `rewrite` 次数 |
| `related_rebuilds` | 8 | `related_leaves` 最多重建几种组合 |
| `related` | 4 | `relate` 每个区域最多试几个算术叶子 |
| `bit_splits` | 4 | `bit_split` 每个区域最多重建几种拆分 |
| `bit_split_budget` | 8 | 每个预处理候选最多几对 `P op Q` |
| `splits` | 4 | `split_bits` 对一个项最多试几个变量位 |
| `split_depth` | 2 | `split_bits` 最多嵌套几层 |
| `split_runs` | 16 | 一次 `split_bits` 最多几次重建 |
| `split_size` | 64 | `split_bits` 只处理不大于此的第一次重建 |
| `block_leaves` | 12 | `small_blocks` 最多处理几个叶子 |
| `block_combos` | 32768 | `small_blocks` 穷举的组合数上限，也是 `wide_blocks` 搜索的步数上限 |
| `cluster_depth` | 2 | `clustered` 最多嵌套几层 |
| `poly_builds` | 512 | `poly_mba` 穷举选择时最多构造几个乘积，之后每层只取第一种 |
| `poly_branch_monos` | 128 | 展开的单项式多于此时，从一开始就每层只取第一种 |
| `polish_rewrites` | 2000 | 一次 `polish` 最多几次未缓存的 `rewrite` |
| `time_limit` | 0 | 默认 `pipeline` 给一次 `simplify` 的毫秒数，到期算截断；0 不限时。bench 用 `-t` 乘以它的 `--time-limit` 比例（默认 0.8）设置，写在 `--passes` 里的 `time_limit=` 优先 |

### 7.3 `sub/NAME`

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

`--passes` 的值是若干**项**，依次作用在 `src/default.pipe` 之上（`default.pipe` 本身也是这样一串项）。

### 8.1 分项

- `;` 总是分项。
- 括号外的空白：后面一段形如 `KEY=`、`KEY+=`、`KEY-=` 或以 `(let` 开头时开始新的一项，否则接在上一项后面。所以 `prepass=lowbits | rewrite extra=0` 是两项，管线里可以有空格。
- `#` 到行尾是注释。

### 8.2 项

| 项 | 含义 |
|---|---|
| `pipeline=P`、`prepass=P`、`polish=P`、`rewrite=P`、`simba=P`、`sub/NAME=P` | 替换这条管线 |
| `polish=a,b,...` | 全是 polish pass 名时：依次尝试这些 `polish/NAME`，变小才保留，有一个变小就重来，至多保留 8 次 |
| `(let NAME P)` | 定义名字，之后的项里写到 `NAME` 的地方展开为 `P`（`a | b` 平铺，`(a | b)` 嵌套，见第 4 节）。`default.pipe` 定义的名字（`first_round`、`later`、`gates`、`rebuild_main`……）也能用 |
| `file=PATH` | 在此处读入文件里的各项 |
| `pre=a,b`、`pre+=`、`pre-=` | 造哪些预处理候选：`unified no_wide split_bits halve_first over_products over_const_bitwise over_shared_bitwise halve_input unclustered` |
| `off=a,b`、`off+=`、`off-=` | 整个运行里关掉的内部 pass（第 5.5 节） |
| `schedule=...`、`schedule+=`、`schedule-=` | 每轮 egglog 的步骤，逗号分隔的 `run:RS`（back-off 调度）、`once:RS`、`sat:RS`（饱和），`RS` 是 `default-ruleset canonicalization constant-folding analysis identity-zero-element simplify` 之一 |
| `match_limit=N`、`ban_length=N` | back-off 调度的参数 |
| `keep=N` | 预处理保留几个候选（至少 1） |
| `extra=N` | 预处理还在改变结果时，额外跑几轮 |
| `printed=N` | 从打印结果再跑几轮（0 不跑） |
| `rerun_input=0/1` | 结果是 `mixed` 时是否带上原输入重跑第一轮 |
| `minimal=0/1` | 是否尝试证明最小 |
| `NAME=N` | 第 7.2 节的限值 |

注意名字是**在读到那一项时展开**的：重新定义 `gates` 不会改变已经读好的 `prepass`，要再写一次 `prepass=...`。

## 9. 检查与警告

读完 `--passes` 后检查，出错时拒绝整个设置：

- 名字：未知的 pass、条件、数、`on`/`off` 名、`with` 的键、`sub/NAME`、规则集，都报错并列出已知的名字。`with` 里写 `off=`，报错并提示 `(off NAME)` 的写法。
- 形式的参数：个数、种类（条件、数、管线）不对。
- 旧的单名写法 `save/t`、`off/NAME`、`egglog/LABEL`，报错并提示括号写法；旧的 `seq(a,b)` 语法报错并提示新写法。
- `egglog`、`reprint` 和次数 `restarts` 只能出现在 `pipeline` 里：只有 `simplify` 的运行才有 e-graph。
- `prepass` 和 `polish` 不能经过别的管线回到自己。调用关系：`prepass` pass 和条件 `opaque`、`rebuilds` 调用 `prepass`；`polish` pass 调用 `polish`；单项 pass、`regions`、`again` 调用 `rewrite`、`simba`、`sub/NAME` 这一组（这一组内部本来就是递归的）。
- 寄存器的读（`load`、`label`、`size`、`same`）前面必须有可能先执行的同名 `save`。按执行顺序算：`if` 的两支都算，`retry` 的条件在 `a` 之后，`best` 的次数在各支之后；`fix`、`wins`、`regions` 的体会重复执行，体里任何地方的 `save` 对整个体都算。这条检查找的是写错名字和顺序，不保证运行时一定有值。

以下只给警告：`eggy1` 和 `bench` 的父进程打印到 stderr，`bench --one` 子进程不打印。

- `--passes` 里定义了却没用到的 `let`。
- 存了却从不读的寄存器。
- 死存储：同一层又 `save` 了一次，中间没读。写在 `if`、`cand`、`first` 的后几支、`retry` 的 `b` 或循环体里的 `save` 不和外面的比较，所以 `(save t) | (if c (save t))` 这种先存默认值再覆盖的写法不算。
- `(off NAME)` 在所在的 seq 里后面没有任何单项 pass，什么也关不掉（只看直接写在 seq 里的 `off`；开关不算）。
- 写在 seq 最后一步的 `(time-limit N)`，什么也限制不了。

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
lowbits | (time-limit 500) | relate | tfunc | (time-limit 0) | finish

# 局部改写：每步只在变小时采用，至多采用 8 次
(scope (with rewrites=polish_rewrites (wins 8
  (smaller polish/push_not polish/push_not)
  | (smaller polish/factor polish/factor))))
```

命令行上：

```bash
eggy1 --show-passes                                         # 当前的全部设置
eggy1 --passes "extra=0 off=relate" -n u32 "expr"
eggy1 --passes "prepass=lowbits | (if mixed rewrite)" -n u32 "expr"
eggy1 --passes "file=my.pipe" -n u32 "expr"
cargo run --release --example bench -- --passes "pre-=halve_input" bench-data/a.txt
python -I scripts/bench-shards.py ... "--passes=off=relate;extra=0"   # 写成一个参数
```
