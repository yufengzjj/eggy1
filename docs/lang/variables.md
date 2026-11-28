# 变量与作用域

## 1. 一条规则

> `NAME = VALUE` 在**当前作用域**里绑定变量 `NAME`；同一作用域里再赋值，就是覆盖这个绑定。读 `NAME` 时先在当前作用域找，没有就沿**调用链**往上找，直到程序的顶层。作用域结束时，它的绑定随之消失。

- 这条规则说的是《[化简库的变量](../lang-lib/variables.md)》的变量（**全局变量**，定义在源文件里，见《[命令行和 --passes](../cli.md)》 第 3 节；Rust 的 pass 也读它们）。给别的名字赋值是**局部变量**（第 5 节）：数、组、函数值都可以存，按词法查找，每次运行一套，不参与这种查找。
- **作用域**有三种：序列（`a | b | ...`，包括分组 `( ... )` 和 `(seq ...)`）、`scope`、每条管线的一次运行。其他形式（`if`、`fix`、`union`、`best`……）不是作用域：`(if C x = 1)` 的绑定落在 `if` 所在的序列里，`(if C (x = 1 | p))` 的绑定只在那条分组序列里。
- "往上"沿调用链走（动态作用域）：`semi_leaves = 2 | polish` 里，`polish` 读到 2，除非它自己在内层再赋值。
- 赋值是没有值的步骤，原样传下收到的值（《[求值](evaluation.md)》 第 2 节），所以可以写在序列的任何位置。
- 赋值右边在执行到这一步时求值，读的是当时的输入。

普通变量是**最内层的绑定起作用**。预算和时限是**链上所有绑定都起作用**：

- **预算**（`rewrites`、`bit_split_budget`）：每用掉一次，链上每一层的绑定都减 1，任何一层到 0 就停。所以退出时外层已经减去了里面用掉的次数，里面赋得再大也超不过外层剩下的。
- **时限**（`time_limit`）：赋值时从此刻起计时，得到一个截止时刻。链上最早的截止时刻起作用，所以里层不能晚于外层。

## 2. 值

- 变量的值是非负整数，或 `none`。每个变量开始时都是 `none`。
- `none` 比所有整数都大（+∞）。上限类变量（`split_runs`、预算、`time_limit`……）读到 `none` 就是不限。
- 布尔值就是数：开关写 1（开）或 0（关），非 0 都算开，比如 `relate = 0`、`cut = 1`。`none` 不是 0，所以作开关时算开：内部 pass 不赋值就是开着的。
- 有上限的变量（`max_leaves` 最多 6）的上限不在 Rust 里，而是 `default.pipe` 的检查 `(let check_limits ...)`：一串 `(assert (NAME <= CAP) "NAME is at most CAP")`。`simplify` 开始时执行它一次（它在定义 `simplify` 时就展开了，之后重新定义 `check_limits` 不影响 `simplify`）。赋值本身不检查；程序给的值超过上限（`none` 也算超过）时 `simplify` 停下，返回这个错误（`max_leaves is at most 6`），所以 `--passes max_leaves=7` 在化简开始时报。管线里的赋值（`(max_leaves = 7 | rewrite)`）不检查，超限的值交给 Rust，后果自负；需要时在赋值后面自己写 `check_limits` 或 `assert`。不经 `simplify` 直接调用 pass 的程序（`(parse s) | prepass`）也不检查。
- 开关不收字面的 `none`（解析时报错）；右边是表达式、算出 `none` 时，开关为开。

## 3. 时限

- 过了截止时刻，调用带 `@timed` 的函数时跳过这次调用，原样返回输入（取元组的函数返回它取的元组，《[元组](tuples.md)》 第 4 节），所以任何时候停下来结果都正确；不带 `@timed` 的函数照常执行。只看这个属性，内置函数（`extern`）和 `def`（`@inline` 的也一样）都是：`(def @timed (f g:group) ...)` 整个跳过，不带它的 `def` 运行函数体，函数体的各步按各自的属性跳过。带 `@timed` 的是计算组的内置函数：单项 pass、alternative、polish pass、`prepass`、`polish`、`egglog`、`take_minimal`、`reprint`、`note`，以及高阶函数 `union`、`best`、`first`、`fix`、`if`、`retry`、`smallest`、`scope`、`regions`、`again`、`tag`、`origin`、`smaller`、`wins`；`default.pipe` 里是 `cand`。不带的有序列、`save`、`label`、`clear`、`take_min`、`filter`、`id`、`none`、`within`、`pre_done`、`assert`、`print`、`parse`、`show`、`settle`、`pipeline`（它的各步各自跳过）、`index`（和序言的 `main`）、数值函数和运算符；`simplify` 也不带，所以 `time_limit = 0` 之后它照常给出输入并记下截断。赋值和 `on`、`off` 不是函数调用，照常执行。所以组变量照常可用，时限所在的作用域结束后，外面的步骤接着运行。跳过算作截断（开关 `cut` 开着时）并计入 `time_limit/skipped`，带 `@uncounted` 的（`note`）不算：过了截止时刻 `note` 什么也不记，之后的计算步骤也都原样返回，所以最后一个真正的结果原样到达 `take_min`。宏 `smallest` 按它的声明（`@timed`）过了截止时刻整个跳过。
- 时限只在步骤之间检查，打断不了正在运行的单个步骤（一轮 egglog、一次大的 `poly_mba` 展开）。一轮 egglog 开始前，按上一轮用的时间估计：估计会超过截止时刻就跳过。
- 开关 `cut` 开着时，因时限跳过的步骤会把整次运行记为截断：`eggy1` 打印提示，bench 把没解出的用例记作 `cut`。默认 `pipeline` 开头写 `cut = 1`。不想算的地方写 `cut = 0`。
- 截断时得到的结果不进缓存。

```
a | time_limit = 1000 | b | time_limit = none | c    # 只限 b
a | (time_limit = 1000 | b) | c                     # 同上
a | time_limit = 1000 | b | c                       # b、c 共用 1000 ms
a | (if ((size main) > 100) time_limit = 200) | b | c   # 输入大时 b、c 共用 200 ms
```

## 4. 宏：`let`、`on`、`off`、`smallest`

宏在解析时展开，不建新作用域：

- `(let NAME p)` 是一项定义，之后写到 `NAME` 的地方展开成 `p`；它就是 `(def @inline (NAME) p)`，平铺、组变量、重新定义的规则见《[函数定义](functions.md)》 第 1、4、6 节。
- `(off A B ...)` 展开成 `A = 0 | B = 0 | ...`，`(on A B ...)` 同理（`A = 1`）；`A`、`B` 必须是开关。它们不是函数：如果是函数，绑定会在返回时撤销。
- `(smallest p)` 展开成 `(clear s) | p' | (take_min s)`。`s` 是宏生成的记录寄存器名（`smallest#N`，每个 `smallest` 一个，用户写不出）。`p'` 是在 `p` 的文字里每个**计算的步骤**后面插一个 `(note s)`：计算的步骤是调用带 `@timed`、不带 `@uncounted`、也不带管线参数的内置函数（单项 pass、alternative、`prepass`、`polish`、`take_minimal`、`reprint`、`egglog`）、调用 `def` 函数，以及 `def` 函数体里的管线参数（记它返回的组）。插入也进到高阶函数的管线参数（`fix`、`best`、`if`、`retry`、`union`、`first`、`smaller`、`wins`、`regions`、`again`、`scope`、`tag`、`origin` 的各支）、组变量绑定的右边（`t = p` 的 `p`）、传给函数的管线参数（闭包，里面的 `note` 写的是外面的 `s`）、有数值参数的 `@inline` 函数体（共享调用处的 `smallest`；体里的管线参数后面不插，参数在调用处已经插过）和里层 `smallest` 的展开里；`let` 和在解析时展开的 `@inline` 函数已展开在文字里，照样插。不进 `def` 函数体和 `prepass`、`polish` 等定义的函数里面：它们只以返回值被看到。所以 `fix` 的各轮、`best` 落选的分支给出的元素都算，输入本身不算。`p` 是序列时展开是一个作用域，否则展开的各步在所在的作用域里执行，和 `p` 不写在 `smallest` 里时一样。`--show-passes` 照原样打印 `(smallest p)`。

每个宏调用（`on`、`off`、`smallest`、在调用处展开的带输入的 `@inline` 函数如 `main`；`let` 和别的 `@inline` 函数的展开直接是所在的文字）解析成一个宏展开节点，记着原样（宏名和参数）和展开后的步骤：运行只跑展开，`--show-passes`、报错、检查和警告看原样。命令行的 `off=a,b`、`off+=`、`off-=` 也展开成这种节点（`(on ...)`、`(off ...)`）。

## 5. 局部变量

给一个不是全局变量（《[化简库的变量](../lang-lib/variables.md)》）的名字赋值，就在本次运行里新建一个**局部变量**；存什么由右边定（第 6 节）：一个数（**数变量**，`n = ((size main) * 2)`，之后 `(fix n p)`、`(if (n > 3) ...)` 读它）、一个组（**组变量**，下面）、一个函数值（**函数变量**，要写类型，`f:term->num = size`，《[函数定义](functions.md)》 第 8 节）。局部变量都按词法查找，规则同下面的组变量；一个名字只存一种（`n is a number variable, so it cannot be bound to a group`、`f is a function variable, so it cannot hold a number`）；不能和全局变量、函数、宏、`let`、`def` 名或参数同名，所以遮不住全局变量。数变量的右边在执行到这一步时、对当时的输入求一次值（`main | n = size | rewrite | (if (n > (size main)) ...)` 比的是 `rewrite` 前后的大小）。

**组变量**存一个组。`R = p` 在当前输入上运行步骤 `p`，把它给出的组绑定到 `R`，输入原样传下去（同其他赋值）；`R = U`（`U` 是组变量）把 `U` 的组绑定到 `R`；`(save R)` 是 `R = id` 的简写；单独写 `R` 是它的值（管线从它开始，《[求值](evaluation.md)》 第 2 节），`(main R)`、`(index I R)` 取它的一个元素（`(size (main R))`、`(same (main R) main)`），`(label R)` 读它的第一个元素。

```
t = (lowbits | unshift) | rewrite | (filter (size < (size (main t))))   # rewrite 的结果比 t 小才留下
(save t) | rewrite | t = (union t id)                            # t 是 rewrite 前后的元素
(save t) | u = t | (u | rewrite)                                 # u 和 t 是同一组
```

- `p` 的步骤是本次运行的步骤：读写本次运行的组变量，外面的 `smallest` 在 `p` 的计算步骤后面照样插 `note`（第 4 节），过了截止时刻 `p` 的计算步骤照常跳过（绑定本身是赋值，照常执行，所以 `R` 得到当时的输入）。`p` 总是一个作用域，只是一步时也是：`t = (off relate)` 的 `off` 到 `p` 结束为止，不影响后面的步骤（所以这样写什么也不做，给警告）。
- 组变量**按词法**查找：每次运行（`pipeline`、`prepass`、`polish`、`def` 的调用……）有自己的一套，不受序列、`scope` 的作用域限制；被调用的 `def` 看不到调用处的组变量，管线参数读写写下它的那次运行的，`@inline` 调用和 `let` 共用调用处的（《[函数定义](functions.md)》 第 3、4 节；在调用处展开的函数体里绑定的组变量，调用之后的文字也能读）。存数的变量沿调用链动态查找（第 1 节），组变量不参与这种查找。
- 同一个名字不能既是存数的变量又是组变量（`(save keep)`、`keep = rewrite` 报错）；写成 `R = p` 时，`R` 也不能是函数、`let`、`def` 名或参数（`rewrite = id` 报错）。
- 读一个没绑定的组变量得空组（`(main R)` 得 `none`，`(size (main R))`、`(same (main R) main)` 得 0）；静态检查要求读之前有可能先执行的绑定（《[检查与警告](errors.md)》）。

`clear`、`note`、`take_min` 用的**记录寄存器**是另一套，和组变量不相通：每个存至多一个项，`(clear R)` 每次打开一个新的 `R`（同名的已经打开时也是），`note`、`take_min` 用最新打开的那个，`take_min` 把它关上。所以 `@inline` 函数在自己的管线参数里再被调用时，两层的 `smallest` 各用各的。记录寄存器和组变量一样属于一次运行，`@inline` 调用共享调用处的。

## 6. 赋值的右边

赋值右边只读一次，读完按它给出的东西定是哪一种：

- 给出数（表达式，包括括号里以数结束的管线 `(rewrite | main | size)`、`((lowbits | main | size) + 1)`）：左边是全局变量（《[化简库的变量](../lang-lib/variables.md)》）时给它赋值，否则绑定一个数变量（第 5 节）。右边的意思只由右边定：`n = (size main)`、`t = (big 3)`、`t = (rewrite | main | size)` 都在当前输入上求出一个数，不是函数值；要存函数值写类型，`f:term->num = size`。表达式读到 `|`、`)` 或项尾为止：`split_runs = (vars main) * 2 | (split_bits (rebuild rewrite))`。
- 给出组：绑定组变量（第 5 节）。右边是**一个步骤**，读到 `|` 或 `)` 为止：`t = rewrite | relate` 是 `(t = rewrite) | relate`；含 `|` 的管线要加括号，`t = (lowbits | unshift)`、`t = (relate = 0 | rewrite)`。右边单独一个不是变量、函数或定义的名字（后面是 `|`、`)` 或项尾）是组变量：`t = u` 把 `u` 的组绑定到 `t`。
- 右边开头的名字两种都说得通时由左边定：`relate` 既是 pass 又是开关变量，`t = relate` 是 pass，`keep = relate` 是开关变量；没注解的参数 `r` 在 `keep = r` 里是数值参数，在 `t = r` 里是给出组的函数（《[函数定义](functions.md)》 第 2 节）。
- 类型对不上是错误，报错写出两边：`keep = (lowbits | unshift)` 报 `keep is a variable that holds a number, so it cannot be bound to a group: (lowbits | unshift) gives a group`；前面绑定过的组变量赋数报 `t is a group variable, so it cannot hold a number: 1 gives a number`；右边像表达式却读不下去时报右边的错（`t = u + 1`，`u` 不是任何名字：`unknown name u in an expression`）。全局变量写错了名字（`kep = 3`）会成为一个新的数变量，由"绑定了却没读"的警告提示（`number variable kep is bound and never read`）。
