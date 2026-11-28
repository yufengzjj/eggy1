# 函数定义

`def` 定义带参数的函数，调用起来和内置函数一样；签名由函数体推出，不用写。

## 1. 写法

```
(def (NAME PARAM ...) BODY)                    # 调用是一次运行（第 4 节）
(def (NAME PARAM ... g:group) g | BODY)        # 最后一个参数 g 是输入：少写时由这一步的输入填入
(def @inline (NAME PARAM ...) BODY)            # 不开运行，在调用处展开
(def @timed (NAME PARAM ...) BODY)             # 过了截止时刻整个跳过（《[变量与作用域](variables.md)》 第 3 节）
(let NAME P)                                   # 即 (def @inline (NAME) P)
pipeline=P、prepass=P、polish=P、rewrite=P、simba=P   # 即 (def (NAME) P)，NAME 见《[化简库的内置函数](../lang-lib/builtins.md)》 第 1 节
```

- `def`、`let` 和 `NAME=P` 一样是 `--passes` 的一项，也是源文件（`default.pipe`、`file=PATH`）的顶层项（《[命令行和 --passes](../cli.md)》 第 3 节），不是管线里的步骤；之后的项里能用它定义的名字。属性写在 `(NAME ...)` 前，顺序随意；别的属性报 `unknown attribute`。
- `BODY` 是三种之一，它的类型就是函数的返回类型（第 5 节）：
  - 管线：返回一个组。
  - 以数结束的管线（`lowbits | main | size`、`g | lowbits | main | size > 3`，《[表达式](expressions.md)》 第 3 节）：返回数。
  - 表达式（以数、`!`、存数的变量、数值函数、返回数的函数或数值参数开头）：返回数。
- 每个函数的最后一个参数是它的**输入**：
  - **简写**：函数体是不以值开头的管线时，输入是隐含的：`(def (NAME P ...) BODY)` 就是 `(def (NAME P ... g:group) g | BODY)`。`default.pipe` 里的定义、`prepass=P` 这样的项、`let` 都是这种。
  - 最后一个参数单独写在函数体开头（没写类型，或写成 `g:group`、`g:term`）时，它是输入：调用少写它时绑定这一步的值（`(f x)` 在 `a | (f x)` 里即 `(f x a)`），写全时就是写出的值。没写类型时，它的类型是接收它的那一步要的输入类型，和值在步骤之间流动时的规则一样：`(def (f p:pipe g) g | p | rewrite)` 的 `p` 要组，所以是 `(f p:pipe g:group) group`，`t | (f lowbits)` 就是 `t | lowbits | rewrite`；`(def (h g) g | size)` 的 `size` 要项，所以是 `(h g:term) num`。只把输入往下传的步骤（赋值、`print`、`assert`、开关）不算接收它，看再下一步。输入是项的函数拿到一个组时，对组里每个元素各运行一次函数体，结果按顺序接起来（《[组、元素和管线](pipeline.md)》 第 2 节的组和元素）。
  - 最后一个参数是组（写成 `g:group`，或由用法推出，如 `(main g)`、`(index 0 g)`、`(p g)`），而函数体是读它的表达式时，它也是输入。`(def (twice p g) (p (p g)))` 的 `g` 由 `(p g)` 推成组，签名是 `(twice p:pipe g:group) group`。
  - 函数体以值开头、最后一个参数不是组时，函数只能写全参数调用，调用是一个不用输入的值（写在 `|` 后面时被丢掉，《[组、元素和管线](pipeline.md)》 第 2 节）。
  - 函数体是读隐含输入的表达式时，函数像内置的数值函数那样取输入：`(def (under k) size <= k)` 是 `(under k:num t:term) num`（第 8 节）。
- 函数体里的名字在读到定义时解析。`let` 和 `@inline` 函数只能用在定义之后，用的是那时的定义（重新定义 `gates` 这样的 `let` 名，不会改变已经读好的 `prepass_steps`）。`def`（不带 `@inline`）在定义之前也能调用，调用在运行时取这个名字最后的定义（第 6 节）：`default.pipe` 里 `rewrite` 和 `simba_steps` 互相调用。
- `--show-passes` 和 `Display` 把 `def` 写在各条管线之前，每个前一行注释是它的签名（`# (twice g:group) group`），照写下的样子打印（除了数和名字，参数都带类型，如 `p:pipe`、`r:group`、`t:term`，这样读回来不变）。`let` 和没有数值参数、不带 `@timed` 的 `@inline` 函数已在使用处展开，不再写出；其他 `@inline` 函数照 `def` 打印（`(def @inline (lim n p:pipe) split_runs = n | p)`）。`--show-builtins` 在最后单列 `def` 的签名，`src/default.pipe` 的（`cand`）和 `--passes` 的各一组。`def` 调用里唯一的、也是最后一个的管线参数照内置函数的写法打印，不加括号（它读到 `)` 为止）。

## 2. 参数

参数有六种，和内置函数的参数类型一样：

| 种类 | 类型 | 推出它的用法 | 调用时 |
|---|---|---|---|
| 管线参数 | `pipe` | 写在步骤位置；当函数值调用（`(p g)`、`g \| p`） | 不求值，原样传进去，是闭包（第 3 节），函数体里每用一次就运行一次 |
| 数值参数 | `num` | 写在表达式里（赋值右边、`(fix N p)`、`(best K ...)`、`(if C ...)`、`filter`、`any`、`all` 的条件……） | 在调用处、对调用时的输入求一次值（同赋值右边） |
| 函数参数 | `term->num`、`group->num`、`term->term`…… | 单独一个名字写在函数类型的参数位置（`(filter pred)`、`(if c p)`）；被调用（表达式里的 `(pred t)`、`t \| pred`）；写注解 | 不求值，是闭包，每次用到时用在给它的输入上（第 8 节） |
| 组参数 | `group` | 写在组变量位置（`(label R)`、`(main R)`、`(size (main R))`）；作函数值或函数的显式输入（`(p r)` 的 `r`）；写注解 `r:group` | 按值：调用处那个组变量的组；最后一个参数是输入时由这一步的组填入 |
| 项参数 | `term` | 只能写注解 `t:term`，或是输入（上面第 1 节）；在函数体里像组参数一样单独写成一个值 | 调用处写一步（`(main r)`、`main`），取它给出的第一个元素；不能用在 `@inline` 函数里 |
| 名字参数 | `name` | 写在名字位置（`(tag NAME p)`、`(origin NAME p)`、`(smaller NAME p)`、`(egglog LABEL)`、`(off NAME)`、`(on NAME)`） | 解析时代入 |

- **类型推断**：没写类型的参数只有一个类型，只从函数体推出（不看调用处，没有默认类型）。函数体里所有用法一起解：
  - 作为参数传给另一个函数时，就是那个参数的类型（`(best 1 p)` 的 `p` 是 `pipe`，`(filter c)` 的 `c` 是 `term->num`）；这种位置先定。
  - 写在步骤位置时是一个函数：它的输入是前一步给出的值的类型，它的结果是下一步要的输入类型；给组变量赋值（`t = p`）要组。两边的类型都还不知道时，它们相同，等别处定下。
  - 输入参数的类型是接收它的那一步要的输入类型（第 1 节）。
  - 这样推不出来时报 `cannot infer the type of p in f: write p:TYPE`：函数体的结尾不要求任何类型，所以 `(def (f n p) rewrites = n | p)`、`(def (f p q) p | q)`、`(def (k g) g)` 都要写类型（`p:pipe`、`g:group`）。`(def (f p g) g | lowbits | p | (best 1 p))` 推得出：`best` 定下 `p:pipe`，`lowbits` 给出的项可以交给它，`g` 是项。
  - 用法互相矛盾时报错，写出两种用法：`parameter p is used as term->num and as pipe`、`parameter p is used as a group or a term and as a step`、`parameter r is used as name and as a step`；写了注解的 `parameter c:term->term is used where term->num is wanted`。函数体里没用到也报错（`parameter q is never used in the body`，写了注解的没用到不报）。
- 可以写类型：`p:pipe`（也可写 `p:group->group`）、`r:group`、`t:term`、`n:num`、`x:name`，以及别的函数类型（`pred:term->num`、`c:group->num`、`f:term->term`，第 8 节）。写了的类型就是它的类型，用法照样要和它接得上。
- 参数只在函数体里看得见（词法绑定），不参与存数变量的查找，不能赋值（`(save a)`、`a = ...`、`n = 3` 都报 `parameter a cannot be assigned`）；不能和变量、函数、宏、`let` 名、`def` 名、`none`、`def`、`let`、`extern` 或函数自己同名，也不能重复。
- 读参数的规则和内置函数一样（《[化简库的内置函数](../lang-lib/builtins.md)》 第 2 节）：数值参数是一个 `earg`（`(f size / 2)` 要写成 `(f (size / 2))`），只有一个管线参数、且它是最后一个参数时读到 `)` 为止，其他管线参数各是一个步骤，组参数和名字参数各是一个名字。个数、种类不对时按个数报错附上签名：`f takes 3 arguments; | gives the last: (f r:group p:pipe g:group) group`；表达式参数处写了管线时还先给出那个表达式的错误。有参数的函数单独写出时报 `NAME needs parentheses`，没有参数的写了参数报 `f takes 1 argument; | gives the last: (f g:group) group`。

**数值参数**是值，不是变量：函数体里读到的是调用时算出的值，函数体先改了输入也不变（`(def (f n p) p | (filter (n == 7)))` 调用成 `(f (size main) rewrite)` 时 `n` 是调用时输入的大小）；被调用的函数看不到它（写了就是未知的名字）；对缓存没有影响（缓存只记读过的全局变量；参数经过赋值影响 pass 时，记下的是被赋值的变量）。赋给有上限的变量时不检查（《[变量与作用域](variables.md)》 第 2 节）；要检查就在赋值后写 `check_limits`（`(def (f n) max_leaves = n | check_limits | rewrite)` 调用成 `(f 8)` 时这次运行报 `max_leaves is at most 6`）。

**名字参数**在解析时代入：每处调用得到一份把名字放进去的函数体，`(off name)` 的参数在调用处检查是不是开关（`unknown off name nope (the argument for n)`）。

**组参数**在函数体里是一个只读的组变量（`(size (main r))`、单独写 `r`）。调用时把调用处那个组变量的组交给函数，所以读写检查在调用处做：`(def (f r:group) (seq r))` 调用成 `(f t)` 而 `t` 没绑定时报 `prepass_steps reads group variable t before it is bound`。`@inline` 函数共用调用处的组变量，组参数在展开时按名字代入，意思相同。

## 3. 值、调用和闭包

值有这几种：数、组、文本、函数值、名字。

- **组值**：组变量（在文字里前面已经绑定过，`(save t)`、`t = ...`）、组参数、函数的组输入，单独写成一个名字时是一个值，给出它的组，不看当前输入。名字不满足这些条件时读成 pass 名（所以写错的名字报 `unknown pass`）。
- **以值开头的管线** `g | a | b` 是这个值依次经过各步的结果，即 `(b (a g))`；不以值开头的管线 `a | b` 是一个函数值。值写在 `|` 后面时被丢掉（《[组、元素和管线](pipeline.md)》 第 2 节）。
- **函数值**：管线参数是 `group → group` 的函数值；`(p g)` 或 `g | p` 调用它，`(p (p g))` 调用两次。

**调用**：

- `a | (f x)` 少写了输入，由这一步的输入填入；显式写全 `(f x g)` 时最后一个参数是输入，可以是组变量名、组参数，或括号里的一步（`(f x (lowbits | unshift))`：以值开头时是那个值经过各步，否则是这一步的输入经过各步，即 `lowbits | unshift | (f x)`）。写全的调用是一个不用输入的值，写在 `|` 后面时它的值被丢掉，要从它开始就写在管线开头或括号里：`((twice rewrite t) | ...)`、`u = (twice rewrite t)`。
- 内置函数也可以显式给输入：`(lowbits t)`、`(minimal t)`、`(mixed (main t))`（输入是 `term?` 时写项，《[化简库的内置函数](../lang-lib/builtins.md)》 第 2 节）；只在写满了参数、后面又是一个值时才这样读（`(if c a u)` 的 `u` 仍是可选的管线参数）。单独的 `main` 写在要项的地方是这一步输入的第一个元素：`(size main)`、`(prepass p main)`。
- 写了参数的函数后面跟一个不是变量、函数或定义的名字时，也读成组变量（在外层绑定的、或写错的），由读写检查判断（`(f x u)` 没有绑定 `u` 时报 `reads group variable u before it is bound`，不报参数个数）；没有参数的函数后面跟这样的名字仍按个数报错（`(lowbits x)`）。
- **隐式输入**：一步的参数里，少写了输入的函数取这一步的输入，所以 `(if ((size main) <= k) p)` 里的 `main` 是这一步输入的第一个元素、`(if (big 3) p)` 里的 `big` 取这一步的组。项上的函数（`size`）取到一个组时报错（《[组、元素和管线](pipeline.md)》 第 2 节的组和元素）。函数体是表达式而读了隐含的输入时（`(def (under k) size <= k)`），函数取隐含的输入，见第 8 节。

**管线参数是闭包**：传进去的管线带着它写下时所在的运行，即调用处的输入、组变量和参数。它在被调用的函数里每用一次就运行一次，但：

- 读写的是调用处的组变量，条件 `input` 指调用处的输入；
- 里面的参数（管线参数和数值参数）指写下它的那个函数的参数，参数再往下传时层层回到写下它的地方：`(def (f n) (g (if ((size main) <= n) x)))` 里的条件在 `g` 里面运行，读的仍是 `f` 的 `n`；
- `smallest` 按文字算：写下它的地方外面的 `smallest` 看得到它里面的步骤，函数体里包住参数的 `smallest` 只看到参数返回的组（《[变量与作用域](variables.md)》 第 4 节）。

没有名字的运行状态跟着它实际运行的位置走：`wins` 的计数、`fix` 的 `moved`、`scope` 的缓存，和内置的 `best`、`wins` 拿到管线参数时一样；所以 `(def (w p) (wins 3 p))` 里 `p` 中的 `smaller` 由 `w` 里的 `wins` 数到。存数的变量沿调用链动态查找（《[变量与作用域](variables.md)》 第 1 节），读的是它运行时的绑定。

组变量的读写检查对管线参数在调用处做：它可能在调用里的任何时候运行，也可能运行多次或不运行（同 `fix` 的体）。

## 4. 运行与展开

**不带 `@inline` 的调用是一次运行**（《[化简库的内置函数](../lang-lib/builtins.md)》 第 1 节的函数也是）：

- 它是作用域：函数体里的赋值、`on`、`off` 在返回时撤销；函数体读得到调用处的绑定（动态作用域）。
- 它有自己的组变量和记录寄存器：调用处的组变量看不到（组参数除外），函数体里绑定的在返回后也看不到。
- 外面的 `smallest` 看不到函数里面，只看到调用给出的组（调用是计算的步骤，《[变量与作用域](variables.md)》 第 4 节）；`wins`、`moved` 只看本次运行。
- 条件 `(input main)` 在函数体里比的是调用时的第一个元素。在 `scope` 里调用时，单项 pass 仍共用那个 `scope` 的缓存。

**`@inline` 函数和 `let`** 不开新的运行，共享调用处的作用域、组变量、记录寄存器和 `smallest`：

- 函数体直接写成 `a | b` 时平铺进所在的序列（调用写成 `NAME` 或 `(NAME ARG ...)` 都是），里面的赋值作用到那条序列的末尾；写成 `(a | b)` 时是一条嵌套的序列，里面的赋值只在这里面有效。
- 没有数值参数、不带 `@timed` 时在解析时展开：管线参数、组参数、名字参数代入，展开后的样子就是调用处的一部分（`(def @inline (g r:group p:pipe) p | (seq r))` 调用成 `(g t rewrite)` 就是 `rewrite | (seq t)`）。函数体以它的组输入开头、别处不读输入时也在解析时展开（序言的 `(def @inline (main g) (index 0 g))`）：写了输入时代入（`(main r)` 是 `(index 0 r)`），没写时用这一步的输入（单独的 `main` 是 `(index 0)`）；它照写下的样子打印（`(main r)`、`main`）。
- 有数值参数时不在解析时展开：调用时先求数值参数，带上自己的参数，函数体照样在调用处的作用域里运行；管线参数照样是闭包。组变量和赋值的检查、警告按展开后的样子在调用处做。
- 有组输入而不能这样展开的（函数体别处也读输入，或有数值参数、`@timed`），每次调用把输入绑定到调用处组变量表里一个它自己的名字（`g#N`，用户写不出），函数体里的 `g` 读它，所以嵌套的调用互不覆盖。

要让赋值影响后面的步骤、共用组变量，或让外面的 `smallest` 看到里面的元素，用 `@inline`；要隔离，用不带属性的 `def`。

## 5. 返回类型

返回类型就是函数体的类型，推出的签名的最后写着它：`(try_without name:name p:pipe g:group) group`、`(big k:num g:group) num`。

- 返回组的函数写在步骤位置；没有参数时写名字，有参数时写 `(NAME ARG ...)`。
- 返回数的函数只能写在要数的地方：`(if (big 3) p)`、`(filter (big 3))`、`keep = (big 3)`、表达式里；也可以作管线的最后一步（《[组、元素和管线](pipeline.md)》 第 2 节）。输入没写时取这一步的输入，写了时是那个组：`(big 3 t)`、`(big 3 (lowbits | unshift))`。没有参数的返回数的函数写在括号里时，`(f)`、`(f t)`、`(f (a | b))` 是调用，`(f < 3)` 是表达式。
- 函数体是表达式时，求值不开新的运行，`@inline` 与否结果一样；函数体是以数结束的管线时，调用是一次运行（同返回组的 `def`），不能带 `@inline`（报 `a function that gives a number is a run of its own, so it cannot be @inline or a let`）。所以 `(def @inline (f) lowbits | main | size)`、`(let f lowbits | main | size)` 报错。
- 函数体里的函数照常在空组和 none 上得 0，所以返回数的函数在空组上也得 0（除非函数体只读变量和参数）。
- 相邻步骤的类型按《[组、元素和管线](pipeline.md)》 第 2 节相接。

## 6. 名字和递归

- 函数名和变量、函数（内置的和已定义的 `def`）、宏、`let` 名不能重复（报 `the name of a pass, form or macro`、`the name of a variable or function`）。`let` 和 `def @inline` 可以重新定义已有的 `let` 名，之后的项用新的定义，已经展开的地方不变；`def` 不能重新定义 `let` 名（`already defined by let or def @inline`），`let` 和 `def @inline` 不能重新定义 `def` 名（`already a function (def (f) ...), which only a def defines again`）。
- **`def` 名是全局的，调用时才取定义**：程序先整个读完、检查，再执行；`def` 的调用在运行时取这个名字**最后的**定义。后面的 `def` 重新定义同一个名字时（同一个或之后的源文本、`import` 的文件、`--passes` 的项），替换它的所有调用，也包括在它之前读好的调用（别的函数的函数体、`default.pipe` 里的、传给 pass 的函数参数）。新的定义要和原来的签名相同：参数的个数和类型、输入、返回类型（参数名和 `@timed` 可以不同），否则报两个签名（`f is defined before as (f g:group) group; a later definition replaces it only with the same signature, not (f n:num g:group) group`）。原来的函数给出组时，新的函数体按给出组的管线读（以数结束报 `gives a number, not a group`）。《[化简库的内置函数](../lang-lib/builtins.md)》 第 1 节的 `pipeline`、`prepass_steps`、`polish_steps`、`rewrite`、`simba_steps` 就这样被替换。
- **先调用后定义**：同一个源文本里，前面的项和函数自己的函数体可以调用后面才定义的 `def`。调用按定义的签名读：先按定义的头读整个源文本（参数都写了类型的，当作给出组的函数），某个定义推出的签名和头给的不同，或因为头不够（有参数没写类型）读不下去时，用第一遍得到的签名再读一遍。两遍都读不下去时（参数没写类型的函数调用自己；互相调用的返回数的函数，头只能当作给出组的函数）报错并说明（`f is called before its definition, where a call reads it by its head: ...`）。
- **递归**：任何 `def` 都可以调用自己，直接、经过别的函数或经过函数参数（`rewrite` 经过 `(again rewrite p)`、`(regions rewrite p)`、`(poly_mba rewrite simba_steps)` 回到自己，`simba_steps` 经过 `peel` 回到自己）。解析时不检查会不会停；运行时嵌套的调用（`def` 的调用、函数值的调用、pass 运行它的函数参数）多于 2000 层时，运行以错误 `recursion deeper than 2000 calls in f` 结束，`f` 是超出的那一层调用的函数（函数值写出它的项），所以 `prepass=lowbits | prepass_steps`、`rewrite=(again rewrite rewrite)` 在运行时报错。正常的程序嵌套的层数和它重建的项的深度相当（deep、Tigress、LLVM 数据上最多 128 层）。剩下的栈不到 1 MB 时，调用在新分配的 8 MB 栈段上继续，所以到 2000 层也不会栈溢出（Windows 主线程的栈只有 1 MB）。

## 7. 错误和警告

解析时报错（《[检查与警告](errors.md)》有全部的检查）：参数名冲突、重复、用法矛盾、没用到、被赋值；未知的类型、属性；推不出参数的类型（`cannot infer the type of p in f: write p:TYPE`）；返回数的函数带 `@timed`；返回数的管线带 `@inline` 或写成 `let`；调用处参数的个数和种类不对（按个数报，附上签名）；返回数的函数写在步骤位置（`f gives a number, not a group`）、返回组的函数写在表达式里（`f gives a group, not a number`）或 `=` 左边（`f is a function and cannot be assigned`）；项上返回数的函数取到组（《[组、元素和管线](pipeline.md)》 第 2 节）；重新定义 `def` 时签名不同；读没绑定的组变量（每个 `def` 的函数体单独检查，组参数和输入算已绑定）。

只给警告：定义了却没用到的函数（`(def (f p n) ...) is never used`）；`|` 后面不用输入的值（《[组、元素和管线](pipeline.md)》 第 2 节）；以及《[检查与警告](errors.md)》对每条管线做的那些检查，对每个 `def` 的函数体也单独做。

## 8. 函数类型和函数值

函数值的类型是 `A->B`：输入 `A` 是 `term` 或 `group`，结果 `B` 是 `num`、`term`、`term?` 或 `group`；`pipe` 就是 `group->group`。多个输入的函数类型（`num->term`、`term->num->num`）报 `a function takes one input, term or group`。

**函数值从哪里来**：

- **部分应用**：少写了最后一个参数（输入）的调用就是函数值，类型是"输入 -> 返回"：`size` 是 `term->num`，`(rewrite_top rewrite)` 是 `term->term`，`rewrite`、`(best 1 a b)` 是 `pipe`，`(big 20)` 是 `group->num`，`(with_budget 8 rewrite)` 是 `pipe`。在步骤位置、表达式里这就是通常的写法（第 3 节的隐式输入）。
- **写在函数类型位置的表达式或管线**：以隐式输入为参数的函数。`(filter (size <= 20))` 的条件对每个元素求值，`(keep_if (size <= 20))` 传进去的也是这样一个函数。
- **函数参数**（第 2 节）和**函数变量**：函数变量是存函数值的局部变量（《[变量与作用域](variables.md)》 第 5 节），要写类型：`f:term->num = size`、`small:term->num = (size <= 20)`、`f:term->num = (under 20)`、`g:term->term = (relate rewrite)`（右边是表达式或一步，类型要接得上）。不写类型时右边的意思只由右边定：`f = size` 是数变量，`t = rewrite` 是组变量。同一个名字只能存一种（`f is a function variable, so it cannot name a group variable`、`t is a group variable, so it cannot hold a function value`）。
- **单独写的函数名**（内置函数和 `def` 一样，解析时就定）：
  1. 位置要函数类型时，是函数值（`(filter size)`、`f:term->num = size`，在程序顶层也是）。
  2. 位置能接它的结果、这一步有输入、它又只少输入（别的参数都写了或没有）时，用在这一步的输入上：`(size main)`、`size + 1`、管线里的 `(print size)` 都求值。
  3. 位置也能接函数值、但求不了值时（没有输入，如程序开头的 `(print size)`；或者还少别的参数，如少 `k` 的 `under`），是函数值；`print` 写它的签名（程序开头的 `(print size under)` 写 `(size t:term?) num (under k:num t:term) num`）。
  4. 位置只能接结果、又求不了值时报错：程序开头的 `size + 1` 报 `size has no input here: the top level of the program starts with none; write its input, as in (size (main t)), ...`。

  "有输入"是静态的：程序顶层开头没有；给出值的一步（组变量、`(parse ...)`、写出输入的调用）之后有，后面的语句也有；赋值把输入原样传下，所以 `u = (parse "x") | ...` 之后仍然没有；`def` 函数体和函数类型的参数里总有。`any`（`print` 的 `x:any...`）两样都接，由 2、3 定；它接数，不接算出来的组，所以给出组的函数（`rewrite`）写在那里总是函数值。写了括号的 `(moved)`、`(h)` 是调用，不算单独写：用在这一步的输入上，程序开头是空组（数值函数得 0）。函数变量写在 `print` 里时写它的名字和类型。
- **返回函数的 `def`**：函数体是表达式而读了隐含的输入时（`(def (under k) size <= k)`），签名是 `(under k:num t:term) num`：输入只读一个项时是 `t:term`，读整组时是 `g:group`。写在要数的地方时取这一步的输入（一个项，`main | (if (under 9) p)`），得一个数；写在函数类型的位置时是 `term->num` 的函数值（`(filter (under 20))`、`(keep_if (under 20))`）。函数体不读隐含输入（`(def (f) keep + 1)`、`(def (big k g:group) (size (main g)) > k)`，后者的输入是 `g`）时照旧返回数。

**调用**：`(pred t)` 或 `t | pred`（表达式里写在括号里，`((pred t) > 5)`、`(t | pred)`），和 `(p g)` 一样；单独写在要数的地方时用在这一步的输入上（`(filter (f < 5))`）。没写注解的参数被这样调用时推成 `group->num`。函数变量的值是闭包：绑定时抓下它读到的局部变量当时的值和调用的参数，在哪里用都一样，之后再给那些变量赋值也不影响它；`(def (f n) small:term->num = (size <= n) | (keep_if small))` 里的 `small` 在 `keep_if` 里面求值时读的仍是 `f` 的 `n`。函数参数传进去的是参数和写下它的运行（第 3 节）。`wins`、`moved`、`scope` 的缓存这些没有名字的状态，按它实际运行的位置算（第 3 节）。

**转换**：传参、存进变量和相邻步骤用同一套规则（《[组、元素和管线](pipeline.md)》 第 2 节的组和元素），给的类型能接到要的类型时隐式转换：

| 要的 | 能给的 | 怎么用 |
|---|---|---|
| `pipe` | `term->term`、`term->term?`、`term->group` | 对每个元素；没有结果时去掉；结果组接起来 |
| `term->num` | `group->num` | 用在只有这一个元素的组上 |
| `term->term?` | `term->term` | 原样 |
| `num` | `term->num`、`group->num` | 用在这一步的输入上（`term->num` 只在输入是一个项时） |

`term->num` 不能给要 `group->num` 的地方（`(when size rewrite)` 报 `size takes t:term? and gives num; its input here is a group ...`；写 `(when (size main) rewrite)`）。参数本身不转换：组不会隐式当作项，要项的参数写 `(main g)`、`(index i g)`、`main`（《[化简库的内置函数](../lang-lib/builtins.md)》 第 2 节）。`size` 声明成 `term?->num` 时作函数值仍是 `term->num`。

接不上时报错写出两边的类型：`each takes f:term->term: (each f:term->term g:group) group; (best 1 rewrite) is pipe`、`keep_if takes pred:term->num: ...; f is term->term`、`f holds term->term; (best 1 rewrite) is pipe`。给数的函数值写在步骤位置报 `f gives a number, not a group: it holds term->num`。

**不做的**：多态（每个参数只有一个类型，`(def (f p) p)` 报 `cannot infer the type of p in f`）；多个输入的函数；在语言里遍历组的元素。

例子（各段都能读进来）：

```
(def (keep_if pred g:group) g | (filter pred))    # (keep_if pred:term->num g:group) group
prepass=(union id rewrite) | (keep_if (size <= 20))

(def (under k) size <= k)                        # 读隐含输入：(under k:num t:term) num
prepass=(union id rewrite) | (filter (under 20)) | main | (if (under 9) (relate rewrite))

(def (each f:term->term g:group) g | f)
prepass=(each (rewrite_top rewrite)) | f:term->num = (size <= 20) | (filter f) | g:term->term = (relate rewrite) | (each g)

(def (pick pred) (save t) | (if ((pred t) > 5) rewrite))   # pred 推成 group->num
prepass=(pick (size main))                                # 对 t 求值：t 的第一个元素的大小

(def (with_budget n p:pipe) rewrites = n | p)
(def (app p:pipe g:group) g | p)
prepass=(app (with_budget 8 rewrite))                     # def 少写最后一个参数

(def (keep_if pred g:group) g | (filter pred))
(def (small_only n) small:term->num = (size <= n) | (union id rewrite) | (keep_if small))
prepass=(small_only 20)                                   # small 在 keep_if 里读 small_only 的 n
```

## 9. 例子

每段是一个独立的例子：

```
(def (twice) rewrite | rewrite)
(def @inline (lb) lowbits | (relate rewrite))
prepass=lb | twice | (finish rewrite)        # 即 lowbits | (relate rewrite) | twice | (finish rewrite)

(def (try_without name p) (best 1 p ((off name) | p)))
prepass=(try_without relate rewrite)         # 即 (best 1 rewrite ((off relate) | rewrite))，在 try_without 的运行里

(def (hold r:group p) p | (union id r))      # (hold r:group p:pipe g:group) group
prepass=(save t) | (hold t (lowbits | rewrite))

(def (f p:pipe) (save t) | p | (seq t))
prepass=(save t) | (f (t | rewrite))         # 参数里的 t 读调用处的 t，f 最后的 (seq t) 读 f 自己的 t

(def (with_budget n p:pipe) rewrites = n | p)
(def (if_small k p) (if ((size main) <= k) p))
(def (f n) (if_small (n * 2) (rewrite | (filter (size <= n)))))
prepass=(f ((size main) / 2)) | (with_budget 8 (relate rewrite))   # n 是调用时输入大小的一半；filter 在 if_small 里运行，读 f 的 n

(def @inline (lim n p:pipe) split_runs = n | p)
prepass=(lim ((size main) - 1) rewrite) | (relate rewrite)    # split_runs 的赋值作用到序列末尾，relate 也读到

(def (f p:pipe g:group) g | p)                   # 输入 g：(f rewrite) 在管线里即 (f rewrite <这一步的组>)
(def (twice p g) (p (p g)))                  # (twice p:pipe g:group) group
(def (big k g:group) (size (main g)) > k)    # (big k:num g:group) num
prepass=(f rewrite) | (save t) | u = (twice (relate rewrite) t) | (if (big 3) (seq u))

(def (size_after) rewrite | main | size)     # 以数结束的管线：(size_after g:group) num
(def (h g:group) g | lowbits | main | size > 3)
(def @inline (k p g:group) g | p | (union id g))
prepass=(if ((t = rewrite | main | size) < size_after) (k rewrite t)) | (filter (h (lowbits | unshift)))
```
