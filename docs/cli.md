# 命令行和 --passes

`--passes` 的值是若干**项**。命令行把每一项写成程序源文本里的一项（下表），排在 `(import "default")`、`-n`、`-m`、`-i` 的赋值之后、化简的语句之前（《[管线语言](lang/README.md)》 第 1 节）；`NAME=VALUE`、`pipeline=P`、`off=a,b` 这样的项只是命令行的简写。

## 1. 分项

- `;` 总是分项。
- 括号外的空白：后面一段以 `KEY=`、`KEY+=`、`KEY-=`、`(let` 或 `(def` 开头，或是一个名字、再后面一段是单独的 `=`（`NAME = VALUE`），且前一段不以 `|` 结尾时，开始新的一项，否则接在上一项后面。所以 `prepass=a | split_runs=4 | b` 是一项，`prepass=a split_runs=4` 是两项。
- `#` 到行尾是注释。

## 2. 项

| 项 | 含义 |
|---|---|
| `NAME=VALUE` | 程序的一项赋值 `NAME = VALUE`，`NAME` 必须是已有的全局变量（写错名字报 `unknown variable`）。值同管线里的写法，可以是表达式。项里的空格只在后一段不像新的一项（不以 `KEY=` 开头）时才接在这一项里：`keep=keep + 1` 是一项（`Display` 就这样写），`keep=keep +1` 也是；要稳妥就不写空格 |
| `NAME = VALUE` | `=` 两边有空格：源文件的写法（第 3 节），`NAME` 还不是全局变量时定义它。`--show-passes` 用它写出 `file=PATH` 定义的变量 |
| `off=a,b`、`off+=a`、`off-=a` | 也是赋值：`off+=a` 是 `a = 0`，`off-=a` 是 `a = 1`，`off=a,b` 是把内部 pass 都设成 1 再关 `a`、`b` |
| `pipeline=P`、`prepass=P`、`polish=P`、`rewrite=P`、`simba=P` | 重新定义 `default.pipe` 的这个函数：`(def (pipeline) P)`、`(def (prepass_steps) P)`、`(def (polish_steps) P)`、`(def (rewrite) P)`、`(def (simba_steps) P)` 的简写（《[化简库的内置函数](lang-lib/builtins.md)》 第 1 节）；`rewrite=P` 不带缓存，要缓存写 `rewrite=(memo rewrite P)` |
| `polish=a,b,...` | 全是 polish pass 名时：依次尝试这些 `polish_NAME`，变小才保留，有一个变小就重来，至多保留 `polish_wins` 次 |
| `(let NAME P)` | 定义名字（《[函数定义](lang/functions.md)》 第 1 节）。`default.pipe` 定义的名字（`first_round`、`later`、`gates`、`rebuild_main`……）也能用 |
| `(def [@inline] [@timed] (NAME PARAM ...) P)` | 定义函数（《[函数定义](lang/functions.md)》） |
| `file=PATH` | `(import "PATH")`（《[管线语言](lang/README.md)》 第 1 节） |
| `pre=a,b`、`pre+=a`、`pre-=a` | 预处理造哪些重建，对开关 `pre_NAME`（《[化简库的变量](lang-lib/variables.md)》 第 1 节）的赋值：`pre=a,b` 把 `pre_a`、`pre_b` 设成 1、其余 `pre_*` 设成 0，`pre+=a` 是 `pre_a = 1`，`pre-=a` 是 `pre_a = 0`；名字是 `unified no_wide split_bits halve_first over_products over_const_bitwise over_shared_bitwise halve_input unclustered` |
| `schedule=...`、`schedule+=`、`schedule-=` | 每轮 egglog 的步骤，逗号分隔的 `run:RS`（back-off 调度）、`once:RS`、`sat:RS`（饱和），`RS` 是 `default-ruleset canonicalization constant-folding analysis identity-zero-element simplify` 之一 |

各项按出现顺序成为程序的项；`schedule` 项没有语言的写法，由命令行直接改程序的调度。`--show-passes` 怎样写出 `def` 见《[函数定义](lang/functions.md)》 第 1 节。顶层的赋值写在表达式之前，那时程序还没有输入，所以读输入的 `split_runs=(vars main)*3` 报 `main has no input here`（要按输入算就写进管线里）；单独的 `vars` 在组上报错（《[组、元素和管线](lang/pipeline.md)》 第 2 节）。

命令行的 `-n T`、`-m N`、`-i N`、`--trace` 也是程序里的赋值（`num_type = T`、`restarts = N`、`iter_limit = N`、`trace = 1`）。

## 3. 源文件

`src/default.pipe` 和 `import` 读的文件都是源文件，由《[管线语言](lang/README.md)》 第 1 节的顶层项组成（`src/builtins.pipe` 只有 `extern` 声明）；`default.pipe` 只写定义：

- 括号形式 `(def ...)`、`(let ...)`（`extern` 只在 `builtins.pipe`），可以跨行；
- 赋值行 `NAME = VALUE`，一行一项，到行尾为止。`NAME` 还不是全局变量时，这一行**定义**它：之后它就是《[变量与作用域](lang/variables.md)》 第 1 节的全局变量，值是这一步赋值的结果；已经是全局变量时，这一行是对它的赋值。两种都是程序顶层的一步，在导入的位置按出现的顺序执行。每个变量开始时都是 `none`，所以 `default.pipe` 里定义成 `none` 的（`rewrites = none`、`time_limit = none`、`restarts = none`、`num_type = none`……）不产生赋值步骤，调用方在程序之前给的值（`run` 的 `globals`）因此留着。
- 语句（《[管线语言](lang/README.md)》 第 1 节），`default.pipe` 里没有。
- `#` 到行尾是注释。

```
keep = 2
cut = 0
max_leaves = 6
semi_leaves = max_leaves
rewrites = none
(let later main | (prepass prepass_steps) | (if minimal take_minimal (egglog later)))
(def (pipeline)
  cut = 1
  | ...)
```

变量名不能和函数、宏、`let`/`def` 名、特征名同名；`prepass_steps = P` 这样给不带参数的函数赋值报错，提示写 `(def (prepass_steps) P)`。`--passes` 的简写对应的完整形式：

| 简写 | 完整形式 |
|---|---|
| `NAME=VALUE` | 赋值 `NAME = VALUE`（只能给已有的全局变量） |
| `file=PATH` | `(import "PATH")` |
| `pipeline=P`、`prepass=P`…… | `(def (pipeline) P)`、`(def (prepass_steps) P)` 等（《[化简库的内置函数](lang-lib/builtins.md)》 第 1 节） |
| `polish=a,b` | `(def (polish_steps) ...)`，函数体同 `default.pipe` 的写法 |
| `off=a,b` | `(on <全部内部 pass>) \| (off a b)` |
| `off+=a`、`off-=a` | `(off a)`、`(on a)` |
| `pre=a,b` | 按定义的顺序给每个 `pre_NAME` 赋值：`pre_a = 1`、`pre_b = 1`，其余 `= 0` |
| `pre+=a`、`pre-=a` | `pre_a = 1`、`pre_a = 0` |

`schedule=` 没有对应的语言形式，只能写在 `--passes` 里。`--passes` 也可以直接写 `(def ...)`、`(let ...)` 和带空格的 `NAME = VALUE`。
