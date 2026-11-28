# 元组

**元组**是固定个数（至少两个）的值放在一起，每个位置有自己的类型，同 Haskell 的元组。它和组是两种值：组是元素（项）的有序集合，重复的只留一个；元组按位置存值，什么都不去掉，位置上可以是数、组、文本、函数值或别的元组。

## 1. 写法和类型

- `(a, b, c)`：圆括号里用逗号隔开的值。靠逗号和调用 `(f x)`、加括号 `(a)` 区分：`(a)` 仍是加括号。名字后面紧跟的 `(`（旧的 `seq(a,b)` 写法）里的逗号不是元组，报 `unexpected character ','`。
- 每个位置读作一个值，规则同赋值的右边（《[变量与作用域](variables.md)》 第 6 节）：
  - 字符串字面量、`(show ...)` 是文本；
  - 元组、存元组的变量、给出元组的函数调用、元组的 `(index i t)` 照它们的类型；
  - 单独一个函数变量或函数参数是函数值；
  - 单独写的函数（内置函数、`def`、`let`，最多只缺它的输入）照《[求值](evaluation.md)》 第 4 节读，各位置用同一个输入（第 7 节）：`t | main | (size, mul)` 给出 `(3, 0)`，程序顶层开头的 `(print (size, 1))` 打印 `(term->num, 1)`。没有要求的类型时（单独一步、赋值的右边）同 `any` 参数。嵌套的元组也一样；
  - 单独一个组变量（或还不是任何名字的名字，读作组变量）是组；
  - 表达式是数；
  - 没写类型的参数单独写在一个位置上时，位置的类型就是参数的类型，由参数的用法推出（《[函数定义](functions.md)》）：`(def (twin n) (n, n + 1))` 的 `n` 是 `num`，`(def (sw2 u) (u, (swap u)))` 的 `u` 是 `swap` 要的 `(num, num)`，`(swap (u, 3))` 让 `u` 取 `swap` 的参数在那个位置上的类型。别处都推不出时报 `cannot infer the type of u in wrap: write u:TYPE`（`(def (wrap u) (u, 1))`），没有默认的类型。
  - 别的是一步，在当前输入上运行，给出组：`((lowbits | unshift), 3)`。含 `|` 的管线要加括号，`(a | b, 1)` 报错。
- 类型写成 `(num, group)`，凡是能写类型的地方都能写：参数 `lims:(num, num, num)`、函数类型里、`extern` 的参数和结果 `(extern (f g:group) (group, num))`。位置的类型是 `num`、`group`、`text`、函数类型或元组类型（`(num, term)` 报 `a tuple holds numbers, groups, texts, functions and tuples, not term`）。

## 2. 读取：`index`

`(index i t)` 的 `t` 是元组时，`i` 必须是写出来的数，结果的类型是元组那个位置的类型，解析时就知道：`(index 0 (1, u))` 是数，可以写在表达式里；`(index 1 (1, u))` 是组，写在步骤位置。超出范围在解析时报错（`(index 2 t) is out of range: (num, num) has positions 0 to 1`），下标不是写出来的数也报错。`t` 是组时 `index` 照旧（下标是任何表达式，给出 `term?`）。同一个函数名，按输入是元组还是组用两条类型规则。

## 3. 绑定

- `t = (1, u)` 绑定一个**元组变量**（局部变量，规则同其他局部变量，《[变量与作用域](variables.md)》 第 5 节）；一个名字只存一种值，元组变量不能再存数、组或函数值，反过来也一样。
- **拆开绑定** `(r, n) = t`：一次给每个位置起一个名字，按位置的类型绑定成组变量、数变量、函数变量或元组变量。名字个数和位置个数不同时报错（`(a, b) = (1, 2, 3) binds 2 names, but (1, 2, 3) is (num, num, num), which has 3 positions`）；名字已经是别的种类的变量时报错（`g is a group variable, so it cannot hold position 1 of (1, 2), which is num`）；文本位置不能绑定（变量只存数、组、函数值和元组）。左边只写名字，不嵌套；要拆里层的元组，再写一次 `(a, b) = d`。

## 4. 函数和管线

- 参数可以是元组：写类型 `t:(num, num)`，或由用法推出（把它传给要元组的参数时，类型就是那个参数的类型，`(def (swap2 u) (swap u))` 推出 `u:(num, num)`）。推断照常：每个参数一个类型，不做多态，元组类型按位置合一。`@inline` 函数不能有元组参数。
- 函数体是元组（或以元组结束）时，函数返回元组：`(def (mk n) (n + 1, n))` 的签名是 `(mk n:num) (num, num)`。返回元组的函数是一次运行，不能带 `@inline`，也不能是 `let`。函数体的位置读这一步的输入时，函数照常取输入：`(def (pair n g:group) (g, n))` 是 `(pair n:num g:group) (group, num)`，`p | (pair 3)` 即 `(pair 3 p)`。
- **在步骤之间传递**：元组怎样在步骤之间传、接它的步骤是哪些，见《[求值](evaluation.md)》 第 2、7 节：`p | (pair 3) | (index 0)`、`(mk 2) | swap | sum`，`(def (f a) (mk a) | (print a) | swap)`。原样传下元组的步骤（`print`、`assert`、赋值）的参数和右边的输入是这个元组，读输入的函数照常报类型错误（`size takes t:term?; its input here is a tuple: (size t:term?) num`）。
- 管线以给出元组的一步结束（或之后只有原样传下它的步骤）时，整条管线给出这个元组（顶层语句、函数体、`t = (... | (mk 3))`）；要组的地方（高阶函数的管线参数等）给元组报错。括号不特殊：括号里给出元组的管线也是元组，写在哪里都一样：`(index 1 ((mk 8) | (print "x")))`、`t = ((mk 1) | keep = 7)`、`((1, 2) | (print "a"))`。
- 打印照写下的样子：`(mk a) | (print a) | (index 1)`。
- **`@timed`**：过了截止时刻跳过的调用给出它的输入（《[变量与作用域](variables.md)》 第 3 节），所以函数给出的要和它取的同类型：给出组的函数，或最后一个参数取的元组类型和返回的元组类型相同的函数（`(def @timed (bump t:(num, num)) ((index 0 t) + 1, (index 1 t)))`，跳过时给出 `t`）。返回元组而输入是组的函数，同返回数的函数一样，不能带 `@timed`（`@timed is for a function that gives what it takes, which a call past the time limit gives instead: a group, or the tuple its last parameter takes`）。

## 5. 打印

`print` 把元组写成 `(v1, v2, ...)`，每个值照 `print` 的写法（组写成各元素的中缀，用 `, ` 隔开；函数值写它的类型）：`(print (1, (parse "x + y"), "a"))` 打印 `(1, (x + y), a)`。程序的结果可以是元组。`show` 不变，仍是项到文本。
