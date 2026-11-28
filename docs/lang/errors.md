# 检查与警告

读完程序后检查，出错时拒绝整个程序（命令行把它报成 `--passes` 的错误）：

- 顶层：还没有值时写了计算组的步骤（《[管线语言](README.md)》 第 1 节）；读了顶层还没有绑定的组变量（`the program reads group variable t before it is bound`）；`import` 写在顶层以外、找不到文件、成环。

- 名字：未知的变量、函数、`on`/`off` 名、规则集，报错并列出已知的名字。名字里的 `-` 读作减号，没法单独报错；解析出错时，如果写了 `a-b` 这样的词，错误后面加上"`a-b` 读作 `a - b`，名字用 `_`"，`a_b` 是已知名字时提示写 `a_b`。
- 类型，照签名（《[化简库的内置函数](../lang-lib/builtins.md)》 第 2 节；`def` 的签名见《[函数定义](functions.md)》 第 5 节）检查，报错时附上签名：管线开头写了数值函数（`mixed gives a number, not a group: (mixed t:term?) num`），表达式里写了组函数（`egglog gives a group, not a number`）；参数的个数、种类（表达式、管线、组变量、名字）不对（`retry takes 4 arguments; | gives the last: (retry c:group->num a:pipe b:pipe g:group) group`）；给出数或文本的一步后面再接一步（`size gives num; rewrite takes g:group`）；项上的函数取到组（`size takes t:term? and gives num; its input here is a group: write the element, as in (size main) or (size (index i r))`）；以数结束的管线写在要组的地方，或括号里的管线写在要数的地方却不以数结束。
- 赋值（《[变量与作用域](variables.md)》 第 6 节）：给函数、参数赋值；开关赋 `none`（开关只收数，0 是关）；右边的类型和左边不合（存数的变量给了组，组变量给了数，报错写出两边）；组变量和存数的变量同名（`(save keep)`、`keep = rewrite`）。条件里写了 `=`（`(if (size = 3) ...)`）报 "an assignment is a step; compare with =="。
- 定义（《[函数定义](functions.md)》）：`let`、`def` 名和变量、函数、宏同名，`def` 重新定义 `let` 名或签名不同的 `def`，`let`、`def @inline` 重新定义 `def` 名（《[函数定义](functions.md)》 第 6 节）；未知的属性、类型；`def` 的参数和已有的名字同名或重复、用法矛盾、没用到；返回数的管线带 `@inline` 或写成 `let`。`(off NAME)` 的名字参数在调用处检查是不是开关。
- `extern` 写在 `src/builtins.pipe` 以外。
- 旧写法报错并提示新写法：`(with KEY=VALUE ... p)`（提示 `(KEY = VALUE | ... | p)`，它的 `bit_splits` 是 `bit_split_budget`）、`(time-limit N)`（提示 `time_limit = N`、`time_limit = none`）、条件名 `true`（提示 `1`，只在组不空时为真的写 `(any 1)`）、单名写法 `save/t`、`off/NAME`、`egglog/LABEL`、`seq(a,b)` 语法，以及带 `/` 的旧名字（`polish/factor`、`sub/cluster`、`semi/bit_split`、`poly/masked`，提示 `names cannot contain '/': write polish_factor`；管线里、`--passes` 的项名和 `off=`、`pre=` 的名字表里、源文件的赋值行里都查）。`with` 外面的 `KEY=VALUE` 就是赋值 `KEY = VALUE`，不报错。
- 递归不检查：运行时嵌套多于 2000 层调用时报 `recursion deeper than 2000 calls in f`（《[函数定义](functions.md)》 第 6 节）。
- 组变量的读（`label`、`main`、`index`、组值）前面必须有可能先执行的、绑定它的 `(save R)` 或 `R = p`（`R = p` 先算右边，所以 `t = (filter (same (main t)))`、`t = t` 报错；`t = u` 是读 `u`）。没绑定过、也不是任何名字的单独一个名字写在步骤位置报 `unknown pass`。每个 `def` 的函数体单独检查（它有自己的组变量，组参数和输入算已绑定），有名字参数的按每种调用代入后的样子检查；`let`、`@inline` 按展开后的样子在调用处检查。管线参数读写调用处的组变量，在调用处检查，当作可能运行多次的体。按执行顺序算：`if` 的两支都算，`retry` 的条件在 `a` 之后，`best` 的个数在各支之后；`fix`、`wins`、`regions` 的体会重复执行，体里任何地方的绑定对整个体都算。这条检查找的是写错名字和顺序，不保证运行时一定有值。

以下只给警告：`eggy1` 和 `bench` 的父进程打印到 stderr，`bench --one` 子进程不打印。

- `--passes` 里定义了却没用到的 `let`、`def`（`(def (f p n) ...) is never used`）。
- `--passes` 的源文件定义了、Rust 代码和任何管线、赋值都不读的全局变量（`NAME is defined and never read`）。

以下几条对每条管线和每个 `def` 的函数体单独检查：

- 新的局部变量名和某个全局变量只差一两个字母（3、4 个字母的名字差 1 个，更长的差 1 或 2 个；编辑距离）：`prepass_steps: number variable kep is a new local variable; did you mean keep?`，和"绑定了却从不读"的警告一起给出，用来发现写错的全局变量名。
- 绑定了却从不读的组变量；同一层又绑定了一次、中间没读的死存储（写在 `if`（`cand`）、`first` 的后几支、`retry` 的 `b` 或循环体里的绑定不和外面的比较，所以 `(save t) | (if c (save t))` 这种先存默认值再覆盖的写法不算）。
- 赋值（包括 `(on NAME)`、`(off NAME)`）是所在序列（或整条管线）的最后一步：什么也影响不到。
- 同一条序列里同一个变量连赋两次，中间只有赋值，也没有读它。
- 不用输入的值写在 `|` 后面（`a | t`、`a | (lowbits t)`、`a | (size (main t))`）：它的值被丢掉（`t does not take the input; its value is dropped — write (t | ...) to start from it`，《[组、元素和管线](pipeline.md)》 第 2 节）。`(seq t)`、`(t | ...)` 和带输入的 `@inline` 调用生成的绑定不警告。

默认管线没有警告，`default.pipe` 的 `let`、`def` 除了给程序调用的 `simplify` 都用到了，Rust 代码读的变量都有定义、`default.pipe` 定义的变量都有人读，执行完 `default.pipe` 后仍为 `none` 的变量（内部 pass 的开关除外）正好是 `rewrites`、`bit_split_budget`、`time_limit`、`trace`，没有命令行时还有 `restarts`、`iter_limit`、`num_type`（都有测试检查）。顶层的项不做警告检查（程序本来就以赋值结束）。
