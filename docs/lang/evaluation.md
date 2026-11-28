# 求值

这里是管线语言怎样求值的唯一说明：输入从哪里来，值怎样在步骤之间传，组和元素怎样相接，单独写的函数名是什么，表达式读什么输入，顶层和元组。别的文档讲各自的主题，用到这些规则时链到这里。

下面的例子都在 `tests/lang/evaluation.pipe` 里运行；用到化简库的函数（`rewrite`、`lowbits`、`size`……）的例子在那里以 `(import "default")` 开头，这里略去。

## 1. 输入

每个函数的最后一个参数是它的**输入**。调用时少写它，就由这一步的输入填入：`a | (f x)` 即 `(f x a)`，`a | f` 即 `(f a)`。写全时，输入就是写出的那个值。

```
(def (add k n:num) n + k)
(print (add 1 2))      # 3
2 | (add 1)            # 3
```

```
t = (parse "x + 0")
(drop_identities t) | main | show    # x，同 t | drop_identities | main | show
```

显式写出的输入可以是组变量、组参数或括号里的一步（《[函数定义](functions.md)》 第 3 节）。

只有输入可以少写。少写了别的参数的调用不是函数值，而是参数个数的错误，附上签名；输入是项或组时后面加上 `| gives the last`：

```
(parse "x") | (fix 3)     # fix takes 3 arguments; | gives the last: (fix n:num p:pipe g:group) group
```

```
(def (add k n:num) n + k)
3 | add                   # add takes 2 arguments: (add k:num n:num) num
```

## 2. 步骤和值的传递

管线 `a | b | c` 的每一步依次求值。步骤之间传的是一个**值**：组、数、文本或元组。一步给不给出值、用不用到输入，解析时就定下。

- **给出值的一步**把它的值往下传，作为下一步的输入，不管它用没用到输入：

  ```
  (def (add k n:num) n + k)
  (parse "x") | 1 | (add 1) | (add 1)                   # 3
  ```

  ```
  (parse "x + y") | main | show | parse | main | show   # (x + y)
  ```

- **没有值的步骤**：`print`、`assert`、赋值（也包括 `(a, b) = ...`）、开关 `(on NAME)`、`(off NAME)`。它们照常执行，把收到的值原样传给下一步：

  ```
  (def (add k n:num) n + k)
  2 | (print "a") | k = 5 | (on lowbits) | (assert (k > 0) "positive") | (add k)   # 写 a，给出 7
  ```

- **括号不特殊**：括号里的管线是一步，给出它最后一步给出或传下的值（组、数、文本或元组），写在哪里都一样。以值开头的括号管线不用外面的输入：

  ```
  (parse "x") | ((parse "y") | (print "a")) | main | show   # 写 a，给出 y
  ```

  ```
  (def (sum t:(num, num)) (index 0 t) + (index 1 t))
  (parse "x") | ((1, 2) | (print "a")) | sum               # 写 a，给出 3
  ```

- **管线可以从任何值开始**：组变量、`(parse ...)`、数、字符串、元组、写全了的调用；括号里的管线也是。

  ```
  "x + y" | parse | main | show    # (x + y)
  ```

  ```
  (def (add k n:num) n + k)
  x = (1 | (add 1))
  (print x ((1) | (add 1)) (1 | (add 1)))   # 2 2 2
  (1 | (add 1)) | (add 1)                   # 3
  ```

  ```
  ("x + y" | parse) | main | show  # (x + y)
  ```

  ```
  (def (sum t:(num, num)) (index 0 t) + (index 1 t))
  (print ((1, 2) | sum))           # 3
  t = (parse "x")
  t | main | show                  # x
  ```

- **用到输入**：一步里某处有一个少写了输入的调用（最外层的，或嵌在参数里、括号里的步骤里的），或者数值参数里有读输入的函数（`(print "size" (size main))`）。不用输入的一步（组变量 `t`、写全的调用、`(parse "x")`、不读输入的表达式、以值开头的括号管线）写在 `|` 后面时，它的值往下传，前一步的值不再用。前一步给出的值没人读过就这样被丢掉时，警告 `... does not use its input; the value of the step before is dropped`：

  ```
  (def (f) main | (parse "y") | main)
  (parse "x") | f      # 警告 f: (parse "y") does not use its input; ...，给出 y
  ```

  管线开头、`(save R)` 之后（它存下了这个值）、读了这个值的赋值或 `print` 之后（`main | (print size) | (parse "y")`）不警告；程序顶层的语句不做警告检查。

- **接不上时报类型错误**，写出两边。下一步要的输入类型和这个值的类型对不上：

  ```
  (parse "x") | 1 | lowbits     # 1 gives num; lowbits takes t:term
  ```

  管线最后一步的值是整条管线的值；以数结束的管线写在要组的地方报 `... gives a number, not a group`。

## 3. 组和元素之间

一个组送进输入是 `term` 的函数时，对组里每个元素各调用一次，结果按原来的顺序收集（第一个元素的结果在前），去掉重复的。按函数的返回：

| 返回 | 结果 |
|---|---|
| `term` | 收集成组；结果不变时保留原元素 |
| `term?` | 给出 none 的元素不收 |
| `group` | 各个结果组按顺序接起来，去掉重复的 |
| 数、文本 | 报错，要写明对哪个元素 |

```
(parse "x + 0") | (union id (parse "x") (parse "y * 1")) | drop_identities   # [x, y]
```

```
(parse "x * y") | (union id (parse "(x | y) - (x & y)")) | small_blocks      # [x ^ y]：x * y 没有结果
```

```
(parse "x") | (union id (parse "y")) | reprint                                # [x, y]
```

```
(parse "x + y") | size     # size takes t:term? and gives num; its input here is a group: write the element, as in (size main) or (size (index i r))
```

没有隐式的"取第一个元素"：要第一个元素写 `main`（或 `(index i r)`），之后这一步给出一个项。

反过来，一个项送进输入是 `group` 的函数时，是只含它的组；`term?` 的 none 是空组。`term?` 也可以给要 `term` 的地方：none 时不调用，数值函数得 0。

```
(parse "x") | (union id (parse "y")) | main | (union id (parse "z"))   # [x, z]
```

```
(parse "x") | none | main | (print size) | (union id (parse "z"))      # 写 0，给出 [z]
```

这条规则在解析时检查（`src/lang/flow.rs`），运行时没有额外的开销。

## 4. 单独写的函数

不带括号、不带参数写出的函数名（内置函数、`def`、`let` 一样），按它所在的位置解读，解析时就定：

1. 位置要函数类型时，是函数值：`(filter small)`、`f:term->num = size`、元组传给 `fs:(term->num, num)` 的参数，在程序顶层也是。
2. 位置能接它的结果、这一步有输入、它又只差输入（没有别的要写的参数）时，用在这一步的输入上，求值。
3. 位置也能接函数值、但求不了值时（这一步没有输入，或者它还少别的参数），是函数值。
4. 位置只能接结果、又求不了值时报错。

```
(def (small) size <= 1)
(parse "x + y") | (union id (parse "x")) | (filter small)    # 规则 1：[x]
```

```
(def (h) size + 1)
(parse "x + y") | main | (print size h (size + 1) rewrite)   # 规则 2：写 3 4 4 (x + y)
```

```
(def (under k) size <= k)
(print size under)                     # 规则 3，没有输入：写 (size t:term?) num (under k:num t:term) num
(parse "x") | main | (print under)     # 规则 3，under 还少 k：写 (under k:num t:term) num
```

```
size + 1      # 规则 4：size has no input here: the top level of the program starts with none; ...
```

求值时照常按第 3 节相接：`(parse "x") | (print size)` 里 `size` 拿到一个组，报 `size takes t:term? and gives num; its input here is a group ...`。

步骤位置不接函数值：顶层开头单独写 `rewrite`、`show`、`t = rewrite` 都按规则 4 报 `... has no input here`。函数类型的位置也不接少了别的参数的函数：`(filter under)` 报 `under needs parentheses: (under ...); (under k:num t:term) num`。

**`any` 位置**（`print` 的 `x:any...`）接所有的值（数、文本、组、元组）和函数值。单独写的函数由规则 2、3 定：有输入时求值，写出结果；求不了值时写它的签名。括号里的写法按它给出的东西读：给出组的调用（也包括写了输入的调用）、括号里的管线给出组，表达式给出数。函数变量写它的名字和类型（`f:term->num`）。

```
t = ((parse "x + 0") | (union id (parse "y")))
(print (drop_identities t) (t | drop_identities) (t | main | size) ((parse "z") | (print "inner")))   # 写 inner，再写 x, y x, y 3 z
```

"有输入"是静态的，见第 6 节；`def` 函数体和函数类型的参数里总有输入。写了括号的 `(moved)`、`(h)` 是调用，用在这一步的输入上；没有输入时和单独写的一样报 `... has no input here`。

## 5. 表达式里的隐式输入

表达式在执行到它的那一刻、对这一步的输入求值。表达式里少写了输入的函数取这一步的输入：`(if ((size main) <= 3) p)` 里的 `main` 是这一步输入的第一个元素。数值参数（`fix`、`wins` 的次数，`best` 的个数，`def` 的数值参数）在调用处、对调用时的输入求一次值。

写在函数类型参数里的表达式，是以隐式输入为参数的函数，输入由接它的函数给：

- `term->num`（`filter`、`any`、`all` 的条件）：给每个元素，各自求值。
- `group->num`（`if`、`retry` 的条件）：给一个组，`if` 是这一步的输入，`retry` 是 `a` 的结果。在 `main |` 之后这一步的输入是一个项，条件拿到的也是这个项。

```
t = ((parse "x + y") | (union id (parse "x")))
(print (t | (filter (size <= 1)) | main | size))                      # 1
(print (t | (if (any (size <= 1)) (filter (size > 1))) | main | size))  # 3
t | main | (if (size > 1) (print "one term after main"))               # 写 one term after main
```

```
t = ((parse "x + y") | (union id (parse "x")))
t | (if (size > 1) none)     # size takes t:term? and gives num; its input here is a group ...
```

函数体是读隐式输入的表达式的 `def`（`(def (under k) size <= k)`），像内置的数值函数那样取输入，见《[函数定义](functions.md)》 第 8 节。

## 6. 顶层

程序的顶层语句连成**一条序列**，依次是它的步骤。

- **开头没有输入**（不是空组）。在还没有值的时候写一个读输入的步骤或调用，检查时报 `... has no input here: the top level of the program starts with none; ...`：

  ```
  (print "hello")                  # 写 hello，程序没有值
  ```

  ```
  rewrite                          # rewrite has no input here: ...
  ```

  ```
  split_runs = (vars main) * 3     # main has no input here: ...
  ```

- **每条语句接着前一条给出的值走**：前面的某一步给出了值，后面的语句就有输入；以值开头的语句（`(parse s)`、组变量）从那个值开始。赋值把输入原样传下，所以只有赋值的语句之后仍然没有输入：`u = (parse "x") | (print size)` 写的是 `size` 的签名。

  ```
  (parse "x + y") | main
  (print size)        # 3
  show                # 程序的值：(x + y)
  ```

- **程序的值**是最后一步给出或传下的值：最后一步是 `print`、`assert` 时是传下的值；最后一步是赋值或开关时，以及从没有一步给出过值时，程序没有值。

  ```
  (parse "x") | (print "a")     # 写 a，程序的值是 [x]
  ```

  ```
  (parse "x") | k = 5           # 程序没有值
  ```

## 7. 元组

- 元组的各位置按第 4 节读：位置要函数类型时是函数值；这一步有输入时用在输入上，几个位置用的是同一个输入；没有输入时是函数值。
- 元组和数、文本一样在步骤之间传：没有值的步骤把它原样传下；`|` 后面不用输入的元组丢掉前一步的值，同第 2 节。
- 给出元组的一步后面，接它的只有 `(index i)`（取那个位置，`i` 是写出来的数）和最后一个参数取同一种元组的函数（元组作为它的输入）。别的步骤报错，写出两边。

```
(def (mk n) (n + 1, n))
(def (swap t:(num, num)) ((index 1 t), (index 0 t)))
(def (sum t:(num, num)) (index 0 t) + (index 1 t))
(def (pair n:num g:group) (g, n))
(print (size, 1))                                   # (term->num, 1)
(print ((parse "x + y") | main | (size, mul)))       # (3, 0)
(print ((mk 2) | (print "a") | swap) ((3, 4) | sum)) # 写 a，再写 (2, 3) 7
(parse "x + y") | (pair 4) | (index 0) | main | show # (x + y)
```

```
(def (pair n:num g:group) (g, n))
(parse "x") | (pair 3) | main     # (pair 3) gives (group, num); main takes g:group
```

元组的写法、类型、`index`、拆开绑定和取元组的函数见《[元组](tuples.md)》。
