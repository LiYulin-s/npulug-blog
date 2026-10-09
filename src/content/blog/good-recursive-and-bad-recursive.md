---
title: 好递归和坏递归
pubDate: 2026-10-09
slug: good-recursive-and-bad-recursive
authors:
  - name: Yurin
    url: https://blog.yurin.top/
---

众所不周知，对于我们的程序分析器而言，你的函数做了什么不重要，但是函数是否收敛对我们很重要。因为如果一个函数收敛，就意味着：

1. 对每个合法输入，我们都可以通过有限步骤的计算得到一个返回值。

2. 如果碰巧这个函数还是纯的，优化器可以进行很激进的优化。例如在严格求值语言中，删除一次结果没有被使用的调用，就不必担心把原本不终止的程序变成会终止的程序。

这里的“收敛”指**终止**；说一个函数收敛，则指它**对每个输入都终止**，也叫全性（totality）。我们先在一个确定性的、图灵完备的计算模型中讨论，把输入和返回值编码为自然数，不考虑异常与外部交互。程序 $f$ 因而计算一个偏函数 $f: \mathbb{N} \rightharpoonup \mathbb{N}$；记 $f(x) \downarrow$ 为有限步内返回，$f(x) \uparrow$ 为永不返回。以下所有量词都在 $\mathbb{N}$ 上取值。

于是，我们非常需要一个**全自动区分递归函数是否收敛的自动测试**。

我们希望找到这样一个判词 $P$，它接收程序 $f$ 的有限代码：

$$
P(f) =
\begin{cases}
  1, & \forall x \; f(x) \downarrow, \\
  0, & \exists x \; f(x) \uparrow.
\end{cases}
$$

“全自动”还要求 $P$ 自己是一个**处处终止的可计算程序**，对每份程序代码都能在有限时间内给出正确答案。否则如果在它拿不准的时候也来一个死循环，我们的分析器就可以和被分析的程序一起挂了。

当然，作为数学上的函数，$P$ 可以这样定义；但是想把它写成程序，康托尔式的对角线就会出来扼杀这种非常好的函数。[^diagonal]

**引理 1（全性不可判定）** 不存在满足上述要求的可计算判词 $P$。

**证明** 程序都是有限字符串，可以按代码有效枚举为 $f_0, f_1, f_2, \ldots$，也可以根据编号模拟它们。这里允许不同代码计算同一个偏函数。假设 $P$ 存在，构造程序：

```ocaml
let d n =
  let code = program_of_index n in
  if p code = 1 then run code n + 1 else 0
```

下文的程序示例统一采用 OCaml 风格记号，数值运算按数学上的自然数解释。这里 `program_of_index n` 取得 $f_n$ 的代码，`run code n` 模拟它在输入 $n$ 上的运行，`p` 表示假设存在的判词 $P$。

先运行 $P(f_n)$：若得到 $0$，直接返回；若得到 $1$，$P$ 的正确性保证 $f_n(n)$ 一定返回，因此加一后也能返回。于是 $d$ 是一个全可计算函数，其程序必定出现在枚举中，设为 $f_k$。那么 $P(f_k) = 1$，所以

$$
d(k) = f_k(k) + 1 = d(k) + 1,
$$

**矛盾** 注意，$d$ 的程序不需要事先知道自己的编号 $k$；它只是把收到的编号 $n$ 当成程序编号和输入各用了一次。$\square$

换个角度看，对给定的程序 $f$，我们希望证明的是这样一个命题：

$$
\operatorname{Total}(f) \; \Longleftrightarrow \; \forall x \, \exists t \; \operatorname{Halt}(f, x, t),
$$

其中

$$
\operatorname{Halt}(f, x, t) \; \Longleftrightarrow \; \text{程序 }f\text{ 在输入 }x\text{ 上至多执行 }t\text{ 步便返回。}
$$

**引理 2（有限步检查可判定）** $\operatorname{Halt}(f, x, t)$ 是一个可判定的关系，并且

$$
\begin{aligned}
  f(x) \downarrow & \; \Longleftrightarrow \; \exists t \; \operatorname{Halt}(f, x, t), \\
  f(x) \uparrow & \; \Longleftrightarrow \; \forall t \; \neg\operatorname{Halt}(f, x, t).
\end{aligned}
$$

**证明** 给定代码、输入和步数上限，只需模拟至多 $t$ 步，检查期间是否返回。这个检查本身总能结束。一次运行终止，当且仅当存在某个有限的步数上限能见证它已经返回；否则它对每个有限上限都没有返回。$\square$

这里的量词顺序不能交换：$\forall x \, \exists t$ 允许运行时间依赖于输入，$\exists t \, \forall x$ 则要求所有输入共享一个固定的步数上限。比如把自然数 $x$ 逐次减一到零的程序总会终止，但运行步数可以任意大。

相应地，全性的否定是

$$
\neg\operatorname{Total}(f) \; \Longleftrightarrow \; \exists x \, \forall t \; \neg\operatorname{Halt}(f, x, t).
$$

“这个输入跑了一万年还没返回”也只检查了一个有限的 $t$，没有证明后面的 $\forall t$。

恭喜，这是一个 $\Pi^{0}_{2}$ 形式的命题。更精确地说，把程序编号作为待判定的输入，全性问题对应集合

$$
\begin{aligned}
  \mathrm{TOT} &= \{e \in \mathbb{N} \mid \operatorname{Total}(f_e)\} \\
  &= \{e \in \mathbb{N} \mid \forall x \, \exists t \; \operatorname{Halt}(f_e, x, t)\}.
\end{aligned}
$$

算术层级中的 $\Pi^{0}_{2}$ 集合，就是可以用“$\forall x \, \exists t$，后接一个可判定关系”的形式定义的集合。上面的式子因此证明了 $\mathrm{TOT} \in \Pi^{0}_{2}$。不过，仅仅写出两个交替的量词，还不能说明问题真的需要这一层：也许存在等价的、更简单的表达式。要说明这里没有这种好运气，还需要补上“完全性”。

**引理 3（全性是 $\Pi^{0}_{2}$-完全问题）** 对任意 $A \in \Pi^{0}_{2}$，都有一个全可计算函数 $g$，使得

$$
a \in A \; \Longleftrightarrow \; g(a) \in \mathrm{TOT}.
$$

这样的 $g$ 称为从 $A$ 到 $\mathrm{TOT}$ 的可计算多一归约，记作 $A \le_m \mathrm{TOT}$。结合 $\mathrm{TOT} \in \Pi^{0}_{2}$，这就是 $\Pi^{0}_{2}$-完全性的含义。[^totality]

**证明。** 由 $A \in \Pi^{0}_{2}$，存在一个可判定关系 $R$，使得

$$
a \in A \; \Longleftrightarrow \; \forall x \, \exists t \; R(a, x, t).
$$

固定 $a$，生成下面这个程序 $F_a$：

```ocaml
let f_a x =
  let rec search t =
    if r a x t then 0
    else search (t + 1)
  in
  search 0
```

其中 `f_a` 对应 $F_a$，`r a x t` 检查 $R(a, x, t)$；$a$ 是生成代码时固定的常量。

每次检查 $R(a, x, t)$ 都会结束，所以

$$
F_a(x) \downarrow \; \Longleftrightarrow \; \exists t \; R(a, x, t).
$$

于是

$$
a \in A \; \Longleftrightarrow \; \forall x \; F_a(x) \downarrow \; \Longleftrightarrow \; F_a\text{ 是全的}.
$$

从 $a$ 生成 $F_a$ 的代码，只需把常量 $a$ 填进上述固定模板，完全不需要先运行 $F_a$。因此可以有效得到它的编号 $g(a)$，而且生成过程总会结束。这就是所需的归约；形式上，这一步也是 $s$-$m$-$n$ 定理的一次应用。$\square$

所以你只需要一台简单的 $0''$ 级别的设备就可以解决这个问题了😋。这里的设备是 $0'$ 能判定普通程序在给定输入上是否停机，$0''$ 则能判定允许查询 $0'$ 的程序是否停机。这个“双撇”也需要解释一下。

**引理 4（全性恰好具有第二次图灵跳跃的难度）**

$$
\mathrm{TOT} \equiv_T 0'', \qquad \mathrm{TOT} \not \le_T 0'.
$$

这里 $A \le_T B$ 表示可以借助判定 $B$ 的预言机来判定 $A$，$\equiv_T$ 表示两个方向都成立。

**证明。** 先证明 $\mathrm{TOT} \le_T 0''$。给定 $f$，构造一个可以查询 $0'$ 的程序 $Q_f$：依次枚举输入 $x = 0, 1, 2, \ldots$，询问 $0'$：“$f(x)$ 是否停机？”遇到第一个否定答案就返回。于是

$$
Q_f^{0'} \downarrow \; \Longleftrightarrow \; \exists x \; f(x) \uparrow \; \Longleftrightarrow \; \neg\operatorname{Total}(f).
$$

$Q_f$ 在这里没有外部输入，上标表示它可用的预言机。向 $0''$ 询问 $Q_f^{0'}$ 是否停机，再将答案取反，就能判定 $f$ 的全性。

反方向用到 $0'' \in \Sigma^{0}_{2}$。令 $z$ 编码一台可查询 $0'$ 的程序及其输入，则存在可判定关系 $V$ 使得

$$
z \in 0'' \; \Longleftrightarrow \; \exists u \, \forall v \; V(z, u, v).
$$

这可以直接从有限计算记录看出来：$u$ 编码一次声称已经停机的预言机计算，记录每次查询及回答，并为所有“会停机”的回答附上普通程序的有限停机见证。$V$ 检查这份记录是否合法，以及所有被回答为“不会停机”的普通程序是否都没有在前 $v$ 步内停机。每次检查都是有限的；对所有 $v$ 都通过，恰好保证那些否定回答也正确。因此，存在这样的 $u$，当且仅当这台 $0'$ 预言机程序确实停机。这也是 Post 定理在第二层的情形。[^jump]

取否定就得到 $\overline{0''} \in \Pi^{0}_{2}$。由引理 3，

$$
\overline{0''} \le_m \mathrm{TOT},
$$

所以借助 $\mathrm{TOT}$ 判定一次归约后的实例，再取反，就能判定 $0''$，即 $0'' \le_T \mathrm{TOT}$。

最后，$0'' \not \le_T 0'$：即使允许查询 $0'$，停机问题的对角线反证仍然成立。假设某个使用 $0'$ 的程序 $H(e, x)$ 能判定所有使用 $0'$ 的程序是否停机，就可以写一个同样使用 $0'$ 的程序 $D(n)$，在 $H(n, n)$ 回答“会停机”时死循环，回答“不会停机”时返回。把 $D$ 自己的编号作为输入，两种回答都会出错。结合前面的等价关系，得到 $\mathrm{TOT} \not \le_T 0'$。$\square$

**推论** 全性和非全性都不能被普通程序半判定。对于全性，不存在一种算法，能在每个全程序上最终确认“全”，同时对非全程序永不误报，即使允许它在非全程序上一直运行。对于非全性，交换这两类程序，结论仍然成立。

**证明** 如果存在其中任意一种算法，用 $0'$ 询问它在给定代码上是否最终确认，再按需要取反，就能判定 $\mathrm{TOT}$，与引理 4 矛盾。这里“确认”可以约定为进入唯一的停机状态，其他情况继续运行。$\square$

这只是证明路上的小小挫折罢了，*我们立刻可以想到非常非常 **practical** 的思路，我们似乎可以只采撷一些低垂果实，把主要的问题留给后人。*

具体来说，我们可以让分析器 $S$ 总会结束，但允许它回答“已证明终止”或“不知道”，并且只要求

$$
S(f) = \text{已证明终止} \; \Longrightarrow \; \operatorname{Total}(f).
$$

这保留了可靠性，放弃了识别所有全程序的完备性。“不知道”并不意味着程序不终止，只意味着它没有通过当前这套充分条件。接下来要找的，就是容易检查、又能覆盖一些有用程序的充分条件。

## 最简单的形式，no recursive

> **最好证明的程序，就是不需要逐个证明的程序。**

既然我们已经决定只采撷一些低垂果实，那么第一批好递归候选人，可以先是不递归的程序。比如：

```ocaml
let inc x = x + 1
let twice x = x + x

let score x =
  let y = inc x in
  if y < 10 then twice y else y
```

只要加法和比较都会结束，这几个函数的终止性几乎没有什么值得讨论的地方：算完一项，再算下一项，选择一个分支，然后返回。分析器甚至不需要理解为什么阈值是 $10$。

不过，“不递归”需要说得稍微严格一点。只检查函数体里没有自己的名字是不够的：

```ocaml
let rec f x = g x
and g x = f x
```

这两个函数都没有直接调用自己，但它们可以互相谦让到宇宙热寂。即使没有任何函数调用，`while true do () done` 也一样不会结束。因此，我们要选出一个确切的语言片段，让无限执行在这里没有藏身之处。

先只保留常量、变量、原语运算、普通的 `let` 绑定、条件分支和具名函数调用：

$$
\begin{aligned}
  e \; ::= {} & c \mid x \mid p(e_1, \ldots, e_n) \mid g(e_1, \ldots, e_n) \\
  & \mid \mathbf{let} \; x = e_1 \; \mathbf{in} \; e_2 \\
  & \mid \mathbf{if} \; e_0 \; \mathbf{then} \; e_1 \; \mathbf{else} \; e_2.
\end{aligned}
$$

这里 $c$ 是自然数或布尔常量，$p$ 是原语，$g$ 是程序中定义的函数。所有表达式都通过通常的类型、变量作用域和参数个数检查；函数的参数与返回值只有自然数和布尔值，调用目标在静态时确定。调用前先求出参数值，`let` 是非递归绑定，`if` 只执行选中的分支。这套语法没有循环、任意跳转或把函数作为值调用的构造。

原语来自一个**事先证明为全的固定清单**，例如自然数上的加法、乘法和比较。检查器只需核对原语名字是否在清单里；一个任意的外部函数不能因为换了个名字，就混进来当作“原语”。这份清单的终止性由语言实现者证明一次。

现在，终止性的第一个拼装规则非常朴素。

**引理 5（有限组合保持终止）。** 在上述语法中，如果一个良类型表达式调用的所有函数都是全的，那么给它的自由变量赋予任意符合类型的值，求值都会在有限步内返回。

**证明。** 对表达式的语法结构归纳。常量和变量直接给出值。对于原语运算和函数调用，先由归纳假设求出有限个参数的值，再由被调用者的全性得到返回值。

对于 `let x = e₁ in e₂`，先由归纳假设求出 $e_1$，用结果扩展变量环境，再对 $e_2$ 应用归纳假设。对于 `if`，先求出布尔条件，然后对选中的分支应用归纳假设。每一种构造都只顺序执行有限次会结束的计算，因此也会结束。$\square$[^finite-syntax]

接下来只剩下一个问题：用户定义的函数，也能像原语一样被一层一层地拼起来吗？

把有限个函数定义作为顶点，建立调用图 $G = (V, E)$，其中

$$
(f, g) \in E \; \Longleftrightarrow \; f\text{ 的函数体中出现了对用户定义函数 }g\text{ 的调用。}
$$

原语已经单独获得了保证，不放进这张图。对于 `if`，两个分支中出现的调用都记为边；这里不需要先判断哪个分支在运行时可达。分析某个入口函数时，收集它及其直接、间接调用的全部定义即可。

**引理 6（无环调用保证终止）。** 对满足上述语法与原语要求的有限程序，如果调用图是有向无环图，那么其中每个函数都是全的。

**证明。** 有限有向无环图可以按“被调用者在前”的逆拓扑顺序排列为 $f_1, \ldots, f_m$，使得

$$
(f_i, f_j) \in E \; \Longrightarrow \; j < i.
$$

这个顺序可以通过反复取出没有出边的顶点得到。如果一个非空的有限图没有这样的顶点，就能一直沿出边走下去，并因顶点有限而重复经过某个顶点，从而得到一个环；这与无环假设矛盾。

按这个顺序归纳。$f_1$ 不调用任何用户定义函数，只能调用全原语，由引理 5，它是全的。假设 $f_1, \ldots, f_{i - 1}$ 都是全的，那么 $f_i$ 只会调用这些已经获得保证的函数和全原语，再次由引理 5，$f_i$ 也是全的。归纳至 $m$ 即得结论。$\square$

前面的例子里，调用边只有

$$
\texttt{score} \to \texttt{inc}, \qquad \texttt{score} \to \texttt{twice}.
$$

按 `inc`、`twice`、`score` 的顺序检查就够了。反过来，$f \to g \to f$ 会在图检查时被发现。我们不需要把函数全部内联，也不需要尝试执行它们。

把入口函数及其调用的全部定义满足上述要求、且调用图无环的程序集合记为 $\mathcal{L}_{\mathrm{nr}}$，现在真的可以写出一个会结束的分析器：

```ocaml
let s_nr code =
  if valid_fragment code && is_acyclic (call_graph code) then
    "已证明终止"
  else
    "不知道"
```

这里 `s_nr` 对应 $S_{\mathrm{nr}}$。`valid_fragment` 收集入口及其直接、间接调用的全部定义，检查类型、作用域、参数个数、允许的语法和全原语清单；`call_graph` 建立这些定义的调用图，`is_acyclic` 检查它是否无环。前一项检查失败时，`&&` 会直接得到否定结果。

它只需检查有限的语法树、核对原语清单，再给有限的调用图做一次拓扑排序。由引理 6，

$$
S_{\mathrm{nr}}(f) = \text{已证明终止} \; \Longrightarrow \; \operatorname{Total}(f).
$$

这就是“不需要逐个证明”的意思：语言的构造规则已经替所有合格程序统一证明了终止性，程序作者只需遵守规则，分析器只需检查这些规则。调用图上的顺序本身就是现成的证明材料。这里也没有绕过第一部分的不可判定性：我们主动限制了能得到肯定答案的程序范围。

当然，这批果实确实低得很踏实。比如自然数上的阶乘：

```ocaml
let rec fact n =
  if n = 0 then 1 else n * fact (n - 1)
```

每次调用把 $n$ 减一，直到遇到零，这个函数会终止；但它的调用图有一条 $\texttt{fact} \to \texttt{fact}$ 的自环，所以当前分析器只能回答“不知道”。它还不理解参数变小了这件事。

于是，下一步就很自然了：允许函数再次调用自己，把调用图上的先后顺序，换成输入上一个有尽头的下降顺序。

## 结构化递归，拆开了再调用

上一节让函数名按照一个不能回头的顺序排列。现在我们允许函数名重复出现，但要求被处理的数据沿着它的真子结构向下走。这就是**结构化递归（structural recursion，也常称结构递归）**。

先把数据范围扩展到有限的列表和树。下面沿用 OCaml 风格的记号；模型里的数据由有限次构造生成，不含循环引用。每次新增一个递归函数，其余可调用函数都已经证明为全，函数体仍然只做上一节那样的有限组合，再加上穷尽的模式匹配。

比如，计算一个列表的长度：

```ocaml
type 'a chain = Nil | Cons of 'a * 'a chain

let rec length xs =
  match xs with
  | Nil -> 0
  | Cons (_, tail) -> 1 + length tail
```

在 `Cons` 分支里，我们已经把输入拆成一个元素和剩余的列表。递归处理的 `tail` 就是刚刚拆出来的部分。它不用经过一次复杂的数学鉴定，来证明自己确实比原来的列表小。

二叉树也一样，而且可以一次递归处理多个子树：

```ocaml
type 'a tree = Leaf | Node of 'a tree * 'a * 'a tree

let rec nodes t =
  match t with
  | Leaf -> 0
  | Node (left, _, right) -> 1 + nodes left + nodes right
```

把通过一次或多次拆解构造子取得的、与原值同属一个递归数据类型的部分称为**真子结构**，记作 $y \triangleleft x$。这里必须至少拆一次，原值本身不算。于是

$$
\begin{aligned}
  \mathit{tail} & \triangleleft \operatorname{Cons}(a, \mathit{tail}), \\
  \mathit{left} & \triangleleft \operatorname{Node}(\mathit{left}, a, \mathit{right}), \\
  \mathit{right} & \triangleleft \operatorname{Node}(\mathit{left}, a, \mathit{right}).
\end{aligned}
$$

**引理 7（有限数据的真子结构关系是良基的）。** 对上述有限归纳数据，不能从某个值出发，沿真子结构关系无限下降。

**证明。** 记 $|x|$ 为把数据展开成有限构造树后的构造子个数。这里也计入 `Nil`、`Leaf`，只统计当前递归结构的节点。例如

$$
\begin{aligned}
  |\operatorname{Nil}| &= 1, \\
  |\operatorname{Cons}(a, xs)| &= 1 + |xs|, \\
  |\operatorname{Leaf}| &= 1, \\
  |\operatorname{Node}(l, a, r)| &= 1 + |l| + |r|.
\end{aligned}
$$

每拆出一个递归字段，都至少去掉了外层的一个构造子，因此

$$
y \triangleleft x \; \Longrightarrow \; |y| < |x|.
$$

无限的子结构下降链将给出自然数的无限严格下降链，而从有限的 $|x|$ 出发不可能一直减下去。等价地，任意非空的数据子集都能选出一个构造子个数最少的元素，它在这个子集中没有更小的真子结构；这就是良基性。$\square$

**引理 8（结构化递归保持终止）。** 设 $f(x, \vec{a})$ 的一个指定参数 $x$ 属于上述有限归纳数据类型。若每次自递归调用 $f(y, \vec{b})$ 都满足 $y \triangleleft x$，其余计算符合前述有限组合与全函数调用规则，那么 $f$ 对所有合法输入终止。

**证明。** 按 $|x|$ 做强归纳，同时对所有合法的辅助参数 $\vec{a}$ 证明终止性。假设所有真子结构 $y$ 上的 $f(y, \vec{b})$，对任意合法的 $\vec{b}$ 都会返回。那么执行 $f(x, \vec{a})$ 时，每个递归调用都会由归纳假设返回；其他原语和函数调用也已经知道会返回。模式匹配只选择一个分支，分支内只有有限组合，所以由引理 5 的同一个论证，整个调用会返回。

没有真子结构的构造子无法产生符合规则的递归调用，因而给出了归纳的起点。于是所有 $x$ 上的调用都会返回。$\square$

注意，我们可以在一个分支中递归调用两次，也可以在递归结果上继续做计算。`nodes left + nodes right` 完全符合要求。需要控制的是每次递归处理的结构；它不必是函数的最后一个动作。

这又给了分析器一件容易做的事情：记录模式匹配拆出了哪些递归字段，追踪普通变量绑定传递的这些关系，再检查每次自调用的指定参数是否来自当前输入的真子结构。比如 `length tail` 可以通过，而 `length (Cons (a, tail))` 把原结构装了回去，不能通过。对于任意计算得到的新值，如果这套检查无法确认其来源，就仍然回答“不知道”。

引理 7 中的节点个数是我们证明检查规则正确的工具，分析器不需要真的计算每个输入的大小。程序作者写下的拆解模式，就已经给出了下降的证据。[^structural]

## 把 nat 用集合搭出来

列表有尾巴，树有子树，看起来都很好拆。那么上一节的阶乘呢？自然数平时长得像一个没有内部结构的标量，`n - 1` 看起来像一次额外的算术操作。

我们可以把一直在使用的自然数换成一个集合论模型，看看里面到底装了什么。在通常的 ZF 集合论里，先定义

$$
0 := \varnothing, \qquad \operatorname{succ}(x) := x \cup \{x\}.
$$

这里的 $x$ 先取任意集合；$\operatorname{succ}$ 表示后继。于是

$$
\begin{aligned}
  0 &= \varnothing, \\
  1 &= \operatorname{succ}(0) = \{0\} = \{\varnothing\}, \\
  2 &= \operatorname{succ}(1) = \{0, 1\} = \{\varnothing, \{\varnothing\}\}, \\
  3 &= \operatorname{succ}(2) = \{0, 1, 2\}.
\end{aligned}
$$

这就是冯·诺依曼的自然数构造：每个自然数都把此前的自然数收进了自己。特别是，每次构造后继时，原来的数会作为一个元素被明确放进去。

但写下 $0, 1, 2, 3, \ldots$ 还需要交代那个省略号。我们希望得到恰好包含这些对象的集合，而不是一个顺便塞进其他东西的大口袋。

称集合 $I$ 为**归纳集**，如果

$$
\operatorname{Ind}(I) \; \Longleftrightarrow \; 0 \in I \; \land \; \forall x \in I \; \operatorname{succ}(x) \in I.
$$

无穷公理保证存在这样的集合。取一个归纳集 $I$，定义

$$
\omega := \bigcap\{J \subseteq I \mid \operatorname{Ind}(J)\}.
$$

交集所取的集合族包含 $I$，所以非空；它又是 $\mathcal{P}(I)$ 的一个子集，因此这里取的是一个集合族的交。我们把 $\omega$ 作为自然数集合 $\mathbb{N}$ 的这个模型。[^nat-sets]

**引理 9（最小归纳集给出自然数归纳法）。** $\omega$ 是包含于每个归纳集的最小归纳集，因此不依赖最初选取的 $I$。对于任意性质 $Q$，有

$$
\begin{gathered}
  \left[ Q(0) \; \land \; \forall n \in \omega \; \bigl(Q(n) \Longrightarrow Q(\operatorname{succ}(n))\bigr) \right] \\
  \; \Longrightarrow \; \forall n \in \omega \; Q(n).
\end{gathered}
$$

**证明。** 参与交集的每个 $J$ 都包含 $0$，所以 $0 \in \omega$。若 $n \in \omega$，那么每个 $J$ 都包含 $n$，也就都包含 $\operatorname{succ}(n)$，故 $\omega$ 本身是归纳集。

对于任意归纳集 $K$，$I\cap K$ 也是 $I$ 的一个归纳子集，因而

$$
\omega \subseteq I\cap K \subseteq K.
$$

这证明了最小性；两个按此方法得到的最小归纳集必定互相包含，故相等。最后，令 $B = \{n \in \omega \mid Q(n)\}$。归纳法的两个前提恰好使 $B$ 成为归纳集，于是 $\omega \subseteq B \subseteq \omega$，即所有自然数都满足 $Q$。$\square$

现在可以认真地把“原来的数就在后继里面”写成一个引理。

**引理 10（自然数可以拆回唯一的前驱）。** 对每个 $n \in \omega$，都有

$$
n \in \operatorname{succ}(n), \qquad n \subsetneq \operatorname{succ}(n), \qquad \bigcup\operatorname{succ}(n) = n.
$$

而且每个非零自然数都唯一地写作 $\operatorname{succ}(k)$，其中 $k \in \omega$。

**证明。** 先由引理 9 归纳证明：每个 $n$ 都是传递集合，即 $x \in n$ 时 $x \subseteq n$，并且 $n \notin n$。这对空集成立。假设它对 $n$ 成立，令 $m = \operatorname{succ}(n) = n \cup \{n\}$。$m$ 的元素要么属于 $n$，要么就是 $n$，两种情况下都是 $m$ 的子集，所以 $m$ 仍然传递。

若 $m \in m$，则要么 $m = n$，由 $n \in m$ 得到 $n \in n$；要么 $m \in n$，结合 $n \in m$ 和 $n$ 的传递性，同样得到 $n \in n$。两者都与归纳假设矛盾，所以 $m \notin m$。

由后继的定义，$n \in \operatorname{succ}(n)$ 且 $n \subseteq \operatorname{succ}(n)$；再由 $n \notin n$，这个包含必定严格。传递性还给出 $\bigcup n \subseteq n$，所以

$$
\begin{aligned}
  \bigcup\operatorname{succ}(n) &= \bigcup(n \cup \{n\}) \\
  &= (\bigcup n) \cup n \\
  &= n.
\end{aligned}
$$

最后，集合

$$
B = \{0\} \cup \{\operatorname{succ}(k) \mid k \in \omega\}
$$

是 $\omega$ 的一个归纳子集：它包含 $0$，而 $b \in B \subseteq \omega$ 时，$\operatorname{succ}(b)$ 又在 $B$ 中。由最小性，$B = \omega$，所以每个非零自然数都是某个数的后继。后继总包含其前驱，故不等于空集；如果 $\operatorname{succ}(k) = \operatorname{succ}(l)$，对两边取并集就得到 $k = l$，因此前驱唯一。$\square$

例如，把 $3$ 拆开：

$$
\begin{aligned}
  \bigcup 3 &= \bigcup\{0, 1, 2\} \\
  &= 0 \cup 1 \cup 2 \\
  &= \{0, 1\} \\
  &= 2.
\end{aligned}
$$

所以，当 $n \ne 0$ 时，我们平时写的前驱 $n - 1$ 在这个模型中满足

$$
n - 1 = \bigcup n, \qquad n - 1 \in n, \qquad n - 1 \subsetneq n.
$$

到了 $0$，就没有可以继续拆出的前驱了。$\bigcup0 = 0$ 虽然仍有定义，却没有发生严格下降，这也解释了为什么必须有零分支。

把这套构造翻译回数据类型，熟悉的 `nat` 就出现了：[^structural]

```ocaml
type nat = Zero | Succ of nat
```

其中 `Zero` 对应空集，`Succ` 对应集合后继。形式上，用保持构造子的编码

$$
\begin{aligned}
  \operatorname{encode}(\texttt{Zero}) &= 0, \\
  \operatorname{encode}(\texttt{Succ}(t)) &= \operatorname{succ}(\operatorname{encode}(t))
\end{aligned}
$$

就能把有限的 `nat` 值和 $\omega$ 一一对应起来。编码的像包含 $0$、对后继封闭，又包含于 $\omega$，由最小性恰好是整个 $\omega$；而 `Zero` 与后继不会混淆，两个后继相等时又能唯一地拆回前驱，对有限构造归纳即可得到编码的单射性。这保证了两种表示既不漏掉自然数，也不会把不同的自然数混成一个。

在这种表示里，$\texttt{Succ} \; k$ 只有一个递归字段 $k$，因此

$$
k \triangleleft \texttt{Succ}(k).
$$

再把阶乘写一遍，下降的证据就直接露在了模式匹配中。这里 `one` 表示自然数 $1$，`mul` 是已经知道为全的自然数乘法：

```ocaml
let one = Succ Zero

let rec fact n =
  match n with
  | Zero -> one
  | Succ k -> mul n (fact k)
```

`fact k` 和 `length tail` 已经是同一种调用方式：把外层构造子拆开，对里面的递归字段继续计算。它直接满足引理 8，不必再为阶乘发明一套专用的终止论证。

| 数据  | 基础构造   | 含有真子结构的构造               | 可递归处理的部分       |
| --- | ------ | ----------------------- | -------------- |
| 列表  | `Nil`  | `Cons (a, tail)`        | `tail`         |
| 二叉树 | `Leaf` | `Node (left, a, right)` | `left`、`right` |
| 自然数 | `Zero` | `Succ k`                | `k`            |

这里的“子结构”有一个具体的对应：数据类型里是 `Succ` 拆出的字段，集合模型里是唯一的前驱元素。任意真子集未必仍是自然数，例如 $\{1\} \subsetneq 3$，但 $\{1\}$ 不传递，所以不是这个模型中的自然数。检查器实际追踪的仍然是合法构造的拆解关系；集合论模型说明了这种关系为什么成立。

于是，**对自然数前驱的递归，就是对 `nat` 的子结构递归。** 数学归纳法里的“假设 $k$ 已经成立”，到了程序里就是“可以使用 `fact k` 的结果”。我们又把每个函数各自要证明的事情，收进了数据的构造规则里。

## 良基，下降到底靠什么收尾

子结构给了我们一个现成的下降方向。再往前走一步，递归参数也可以由计算得到：只要能证明它沿着某个有尽头的关系下降，终止证明仍然可以复用。

设 $D$ 是调用状态的集合，$R \subseteq D\times D$，约定 $y \, R \, x$ 表示允许从状态 $x$ 递归到状态 $y$。如果有多个相互调用的函数，可以把函数名也放进状态里。

称 $R$ **良基（well-founded）**，如果每个非空子集都有一个 $R$-极小元：

$$
\operatorname{WF}(R) \; \Longleftrightarrow \; \forall B \subseteq D \; \left[ B \ne \varnothing \Longrightarrow \exists m \in B \; \neg\exists y \in B \; (y \, R \, m) \right].
$$

“极小”在这里表示：在当前这个 $B$ 里面，已经找不到它的前驱。它不要求 $m$ 能和 $B$ 中的每个元素比较。

这个定义立即排除了无限下降链

$$
x_0 \; \longleftarrow_R \; x_1 \; \longleftarrow_R \; x_2 \; \longleftarrow_R \; \cdots, \qquad x_{i + 1} \, R \, x_i,
$$

因为链上所有元素组成的集合没有极小元。对于本文可以编码为自然数的调用状态，反过来也成立：如果某个非空 $B$ 没有极小元，就从编号最小的元素开始，每次从 $B$ 中取编号最小的 $R$-前驱，得到一条无限下降链。这里的选取用于数学证明，并不要求我们能计算出那个反例集合。

良基性也比“没有环”更强。在整数上，$0, -1, -2, \ldots$ 可以一直严格下降，整个过程中没有重复一个状态。有限调用图中的无环检查能解决问题，靠的是那张图还有“有限”这个条件。

**引理 11（良基归纳）** 若 $R$ 良基，则对任意性质 $Q$，有

$$
\begin{gathered}
  \left[ \forall x \in D \; \left( \bigl(\forall y \in D \; (y \, R \, x \Longrightarrow Q(y))\bigr) \Longrightarrow Q(x) \right) \right] \\
  \Longrightarrow \forall x \in D \; Q(x).
\end{gathered}
$$

**证明** 假设结论不成立，令 $B = \{x \in D \mid \neg Q(x)\}$，并取其中一个 $R$-极小元 $m$。$m$ 的每个 $R$-前驱都不在 $B$ 中，因此全部满足 $Q$。由前提得到 $Q(m)$，与 $m \in B$ 矛盾。$\square$

让 $Q(x)$ 表示“从状态 $x$ 发起的调用会返回”，这个归纳原则就变成了终止证明：只要较小状态上的递归调用都返回，当前调用剩余的有限计算也会返回。

实际使用时，我们通常不会直接研究所有状态之间的关系，而是给状态附上一个**下降度量（ranking function）**。

**引理 12（下降度量保证终止）** 设 $\prec$ 是集合 $W$ 上的良基关系，$\rho: D \to W$。若每次递归调用从 $x$ 转到 $y$ 时都有

$$
\rho(y) \prec \rho(x),
$$

并且除这些递归调用外，函数体只做有限组合、穷尽的分支处理和已知会终止的计算，那么所有合法调用都终止。

**证明** 定义 $y \, R_\rho \, x$ 当且仅当 $\rho(y) \prec \rho(x)$。对任意非空 $B \subseteq D$，在像集 $\rho[B]$ 中取一个 $\prec$-极小元，并选取映到它的 $m \in B$。$m$ 不可能在 $B$ 中有 $R_\rho$-前驱，否则它的像就不是极小元。因此 $R_\rho$ 良基。

现在对“调用会返回”使用引理 11：所有递归调用的状态都更小，因而由归纳假设返回；函数体剩余的有限计算也会结束。$\square$

例如，欧几里得算法可以写成

```ocaml
let rec gcd a b =
  if b = 0 then a else gcd b (a mod b)
```

这里输入是自然数；取余只在 $b > 0$ 的分支执行，并且该运算会终止。递归参数中的余数是算出来的，我们可以用

$$
\rho(a, b) = b, \qquad 0 \le a \bmod b < b\quad(b > 0)
$$

证明它下降。于是每次调用都有

$$
\rho(b, a \bmod b) < \rho(a, b),
$$

直接套用引理 12 即可。证明的工作从“追踪任意长的执行”，变成了“找一个良基度量，检查每条递归边上的下降”。分析器可以尝试合成这样的度量，程序作者也可以提供它；无法确认下降时，仍然回答“不知道”。

## 偏序、全序、良序，分别多要求了什么

现在把这些经常一起出现的“序”分清楚。**偏序**通常用非严格记号 $\preceq$，要求自反、反对称和传递：

$$
\begin{aligned}
  x & \preceq x, \\
  x \preceq y \; \land \; y \preceq x & \Longrightarrow x = y, \\
  x \preceq y \; \land \; y \preceq z & \Longrightarrow x \preceq z.
\end{aligned}
$$

它允许两个元素互不比较。例如集合的包含关系 $\subseteq$ 是偏序，而 $\{0\}$ 与 $\{1\}$ 互不包含。

对应的**严格偏序**定义为

$$
x \prec y \; \Longleftrightarrow \; x \preceq y \; \land \; x \ne y.
$$

讨论下降的良基性时，我们检查的是这个严格部分。自反的 $\preceq$ 本身会允许 $x \preceq x \preceq x \preceq \cdots$；因此终止条件必须要求严格下降。

如果再要求任意两点都能比较，得到的就是**全序（total order，也称线性序）**：

$$
\forall x, y \in D \; (x \preceq y \; \lor \; y \preceq x).
$$

全序只保证我们能分出先后。整数上的通常大小关系是全序，负方向却可以一直走下去。

这里还要区分**极小元**和**最小元**。对非空 $B \subseteq D$，

$$
\begin{aligned}
  m\text{ 是极小元} & \; \Longleftrightarrow \; m \in B \; \land \; \neg\exists y \in B \; (y \prec m), \\
  m\text{ 是最小元} & \; \Longleftrightarrow \; m \in B \; \land \; \forall y \in B \; (m \preceq y).
\end{aligned}
$$

在包含偏序中，$B = \{\{0\}, \{1\}\}$ 的两个元素都是极小元，却没有最小元。在全序中，极小元一定是最小元：对任意 $y$，可比较性保证要么 $m \preceq y$，要么 $y \prec m$；后一种情况已被极小性排除。

**良序（well-order）** 是每个非空子集都有最小元的全序。因此

$$
(D, \preceq)\text{ 是良序} \; \Longleftrightarrow \; \preceq \text{ 是全序，且其严格部分 } \prec \text{ 良基}.
$$

良基关系本身不必是严格偏序：例如 $R = \{(0, 1), (1, 2)\}$ 是良基关系，却不传递，因为 $(0, 2) \notin R$。它已经足够支持引理 11 和引理 12。程序的递归依赖只需要良基，不要求所有状态都能排在同一条线上。[^orders]

下面这些关系都是偏序，但另外两个条件各不相同：

| 集合与关系 | 是全序吗 | 严格部分良基吗 | 是良序吗 |
| --- | --- | --- | --- |
| $\mathbb{N}$ 上的 $\le$ | 是 | 是 | 是 |
| $\mathbb{Z}$ 上的 $\le$ | 是 | 否 | 否 |
| 自然数的有限子集，按 $\subseteq$ 排序 | 否 | 是 | 否 |
| $[0, 1]$ 上的 $\le$ | 是 | 否 | 否 |

有限集合每次严格缩小时，元素个数也严格减少，所以第三行良基。而第四行即使有下界，仍然允许 $1, \frac{1}{2}, \frac{1}{4}, \ldots$ 无限下降。“有下界”和“良基”之间还差着这条无限链。

良序也可以比一个自然数计数器更灵活。例如在 $\mathbb{N}^2$ 上定义第一坐标优先的**字典序**：

$$
(a, b) \prec_{\mathrm{lex}} (c, d) \; \Longleftrightarrow \; a < c \; \lor \; (a = c \; \land \; b < d).
$$

**引理 13（自然数对的字典序是良序）** 上述严格字典序加上相等关系，得到 $\mathbb{N}^2$ 上的良序。

**证明** 比较第一坐标，只有相等时才比较第二坐标，由自然数序的性质可得全序。对任意非空 $B \subseteq \mathbb{N}^2$，先取所有第一坐标中的最小值 $a_0$，再取满足 $(a_0, b) \in B$ 的第二坐标中的最小值 $b_0$。那么 $(a_0, b_0)$ 就是 $B$ 的字典序最小元。$\square$

当第一坐标减少时，第二坐标可以增大任意多。一个经典例子是 Ackermann 函数，记作 $A$，代码中写作 `ack`：

```ocaml
let rec ack m n =
  match m, n with
  | 0, n -> n + 1
  | m, 0 -> ack (m - 1) 1
  | m, n ->
      let r = ack m (n - 1) in
      ack (m - 1) r
```

对于最后一个分支，把输入写成 $(m + 1, n + 1)$，内层调用的参数满足

$$
(m + 1, n) \prec_{\mathrm{lex}} (m + 1, n + 1).
$$

由良基归纳，它会得到一个自然数结果 $r$。外层调用的参数则满足

$$
(m, r) \prec_{\mathrm{lex}} (m + 1, n + 1),
$$

无论 $r$ 有多大。第二个分支也因为第一坐标减少而下降，第一个分支直接返回。因此这个定义对所有自然数输入终止。

字典序中的 $(1, 0)$ 前面有 $(0, 0), (0, 1), (0, 2), \ldots$，却没有一个紧挨着它的直接前驱。良序允许这样的情况；递归时我们只需选择更小的状态，并不需要每次都能执行某种统一的“减一”。

## 不动点，函数也可以是方程的未知数

我们一直在证明递归如何结束。现在看看递归定义本身说了什么。

把阶乘函数体里的递归调用临时换成一个候选偏函数 $p$，得到一个把函数映到函数的算子：

$$
(\Phi(p))(n) =
\begin{cases}
  1, & n = 0, \\
  n \cdot p(n - 1), & n > 0.
\end{cases}
$$

这里沿用严格求值：如果 $p(n - 1)$ 没有返回，乘法也没有结果。阶乘的递归方程恰好要求

$$
f = \Phi(f).
$$

对于一个算子 $\Phi: L \to L$，满足 $\Phi(u) = u$ 的元素 $u$ 就叫它的**不动点（fixed point）**。上面这个不动点的对象是整个函数：把递归调用按函数体展开一层，得到的行为仍然相同。

不过，给出一个算子，并不能保证它有不动点。自然数上的后继算子 $n \mapsto n + 1$ 就没有不动点，尽管自然数本身还是良序。要保证不动点存在，我们需要研究偏序中的另一种性质：**完备性**。

在偏序 $(L, \sqsubseteq)$ 中，集合 $B$ 的上界是大于等于 $B$ 中每个元素的点；上界中的最小元叫**上确界**，记作 $\bigvee B$。对偶地，下界中的最大元叫**下确界**，记作 $\bigwedge B$。

每两个元素都有上确界与下确界的偏序叫**格**。如果每个子集都具有这两种确界，包括空集，那么它叫**完备格（complete lattice）**。特别地，它有最小元和最大元：

$$
\bot_L = \bigvee\varnothing, \qquad \top_L = \bigwedge\varnothing.
$$

例如，幂集 $(\mathcal{P}(I), \subseteq)$ 是完备格，上确界是并集，下确界是在 $I$ 内取交集，最小元是 $\varnothing$，最大元是 $I$。完备格并不要求全序；而实数区间 $[0, 1]$ 是一个全序的完备格，它的严格部分仍然不良基。

**引理 14（Knaster–Tarski 最小不动点定理）** 若 $L$ 是完备格，$\Phi: L \to L$ 单调，即

$$
x \sqsubseteq y \; \Longrightarrow \; \Phi(x) \sqsubseteq \Phi(y),
$$

则 $\Phi$ 存在最小不动点，并且

$$
\mu\Phi = \bigwedge\{x \in L \mid \Phi(x) \sqsubseteq x\}.
$$

**证明** 令 $C = \{x \in L \mid \Phi(x) \sqsubseteq x\}$，$a = \bigwedge C$。由于 $\top_L \in C$，$C$ 非空。对任意 $c \in C$，由 $a \sqsubseteq c$ 和单调性得到

$$
\Phi(a) \sqsubseteq \Phi(c) \sqsubseteq c.
$$

所以 $\Phi(a)$ 是 $C$ 的下界，从而 $\Phi(a) \sqsubseteq a$。再次使用单调性，得到 $\Phi(\Phi(a)) \sqsubseteq \Phi(a)$，即 $\Phi(a) \in C$。既然 $a$ 是 $C$ 的下界，就又有 $a \sqsubseteq \Phi(a)$，因此 $\Phi(a) = a$。

任何不动点 $q$ 都属于 $C$，故 $a \sqsubseteq q$，这就证明了最小性。$\square$[^tarski]

回到刚才构造自然数时选取的归纳集 $I$，在它的幂集上定义

$$
T: \mathcal{P}(I) \to \mathcal{P}(I), \qquad T(X) = \{0\} \cup \{\operatorname{succ}(n) \mid n \in X\}.
$$

$I$ 对后继封闭，所以 $T$ 的结果仍在 $\mathcal{P}(I)$ 中；$X \subseteq Y$ 时显然有 $T(X) \subseteq T(Y)$。而

$$
T(X) \subseteq X \; \Longleftrightarrow \; \operatorname{Ind}(X).
$$

于是，引理 14 直接给出

$$
\begin{aligned}
  \mu T &= \bigcap\{X \subseteq I \mid \operatorname{Ind}(X)\} \\
  &= \omega.
\end{aligned}
$$

上一节取的最小归纳集，原来就是集合生成算子的最小不动点。$T$ 处理的是一整个候选集合：把零放进去，再把已有元素的后继放进去。到了 $\omega$，这套构造规则便不再增加新元素。

## 最小不动点，逐步补全一个递归函数

为了给程序本身解释不动点，我们也需要给偏函数排序。

引入一个不属于自然数的新符号 $\bot$，用它记录“没有返回值”。在某个近似阶段，$\bot$ 表示这一阶段尚未确定结果；在程序的完整语义中，它表示该输入上的运行不终止。记

$$
\mathbb{N}_\bot = \mathbb{N} \cup \{\bot\}, \qquad \mathcal{D} = \{p: \mathbb{N} \to \mathbb{N}_\bot\}.
$$

这里 $\mathcal{D}$ 包含所有这样的数学函数，用来表示所有从自然数到自然数的偏函数。定义**信息序**：

$$
p \sqsubseteq q \; \Longleftrightarrow \; \forall n \in \mathbb{N} \; \bigl(p(n) \ne \bot \Longrightarrow q(n) = p(n)\bigr).
$$

它表示 $q$ 保留 $p$ 已有的返回值，并且可以在更多输入上给出结果。两个不同的确定结果互不比较；例如在同一个输入上返回 $3$ 和返回 $4$，是两份不相容的信息。处处取 $\bot$ 的函数是最小元，记作 $\bot_{\mathcal{D}}$。

这确实是偏序：每个函数扩张自己；若两个函数互相扩张，就在每个输入上完全相同；扩张关系也显然传递。

对于任意可数递增链

$$
p_0 \sqsubseteq p_1 \sqsubseteq p_2 \sqsubseteq \cdots,
$$

它的上确界可以逐点拼出来：

$$
\left(\bigsqcup_{k \in \mathbb{N}}p_k\right)(n) =
\begin{cases}
  v, & \exists k \; p_k(n) = v \in \mathbb{N}, \\
  \bot, & \forall k \; p_k(n) = \bot.
\end{cases}
$$

一旦某个阶段给出了 $v$，后续阶段就只能保留 $v$，所以这个定义不会冲突。它包含链上每个函数的全部信息；任何共同上界又必须包含这些信息，因此它确实是最小的上界。

这样的结构称为**带最小元的 $\omega$-完备偏序**。这里不要求任意一组元素都有共同上界：例如 $p(0) = 0$、$q(0) = 1$ 时，就不存在同时扩张两者的偏函数。因此 $\mathcal{D}$ 不是完备格，不能直接把引理 14 原封不动地套上去。[^domains]

对每个候选 $p$，函数体都确定了一份偏函数 $\Phi(p)$；没有返回的输入记为 $\bot$，仍然是这个语义空间中的合法结果。这个数学上的记法没有要求我们先判断运行会不会终止。

程序的算子还能提供额外的条件。若 $\Phi: \mathcal{D} \to \mathcal{D}$ 单调，并且保持可数递增链的上确界：

$$
\Phi\left(\bigsqcup_k p_k\right) = \bigsqcup_k\Phi(p_k),
$$

就称它为 **$\omega$-连续算子**。

对于本文通过普通调用取得递归结果的确定性程序，这个条件来自计算的有限性。若用更完整的候选函数替换 $p$，已经获得的调用结果都不会改变，所以已经返回的计算仍然返回同一个值，这给出单调性。

进一步说，若在 $\bigsqcup_k p_k$ 提供的结果下，函数体能够返回，那么这次有限执行只查用了有限多个调用结果。每个结果都已在链的某个阶段出现，取这些阶段编号的最大值 $K$（没有查询时取 $K = 0$），就能在 $p_K$ 下重现整次返回。因此结果不会等到所有有限阶段之后才凭空出现，这给出上述连续性等式。

**引理 15（Kleene 最小不动点定理）** 在带最小元的 $\omega$-完备偏序上，$\omega$-连续算子 $\Phi$ 的最小不动点是

$$
\mu\Phi = \bigsqcup_{k \in \mathbb{N}}\Phi^k(\bot).
$$

这里的 $\bot$ 表示该偏序的最小元。对偏函数空间，它就是 $\bot_{\mathcal{D}}$。

**证明** 令 $u_0 = \bot$，$u_{k + 1} = \Phi(u_k)$。由最小元性质，$u_0 \sqsubseteq u_1$；再由单调性归纳可得 $u_k \sqsubseteq u_{k + 1}$。因此 $u = \bigsqcup_k u_k$ 存在，并且由连续性，

$$
\begin{aligned}
  \Phi(u) &= \Phi\left(\bigsqcup_k u_k\right) \\
  &= \bigsqcup_k\Phi(u_k) \\
  &= \bigsqcup_k u_{k + 1} \\
  &= u.
\end{aligned}
$$

若 $q$ 是任意不动点，由 $u_0 \sqsubseteq q$ 出发，反复使用单调性可得

$$
u_{k + 1} = \Phi(u_k) \sqsubseteq \Phi(q) = q.
$$

所以所有 $u_k$ 都小于等于 $q$，其上确界 $u$ 也小于等于 $q$，即 $u$ 是最小不动点。$\square$[^kleene]

连续性在这里承担了实际工作。比如在自然数上方加入两个点，按

$$
0 < 1 < 2 < \cdots < \omega < \top
$$

排列，并定义 $F(n) = n + 1$、$F(\omega) = \top$、$F(\top) = \top$。这个偏序是完备格：无界的自然数子集以上方的 $\omega$ 为上确界，其余确界也都存在。$F$ 是单调的，但从 $0$ 出发的有限迭代的上确界是 $\omega$，而 $F(\omega) = \top \ne \omega$。它没有保持这条链的上确界，所以不满足引理 15 的连续性条件。引理 14 保证的最小不动点在这里是 $\top$。

对于递归程序，$u_k = \Phi^k(\bot_{\mathcal{D}})$ 可以理解为允许递归展开 $k$ 层，超出部分暂记为 $\bot$。任何真正返回的运行只会用到有限的展开层数，因而会出现在某个 $u_k$ 中；反过来，某个 $u_k$ 已经给出的返回值，也对应原程序的一次有限执行。因此，这些近似的上确界恰好收集了程序所有实际能够返回的结果。

拿阶乘的算子试一下：$u_0$ 在任何输入上都没有结果，$u_1$ 只知道 $0! = 1$，$u_2$ 又知道 $1! = 1$，再往后逐步得到 $2!, 3!, \ldots$。由归纳可得

$$
u_k(n) =
\begin{cases}
  n!, & n < k, \\
  \bot, & n \ge k.
\end{cases}
$$

因为零分支直接给出 $1$，而非零输入 $n$ 在下一阶段得到结果，当且仅当前一阶段已经得到 $n - 1$ 的结果。于是每个输入 $n$ 都在第 $n + 1$ 个近似中获得返回值，最小不动点就是全的阶乘函数。

这里没有一个有限阶段已经补全了所有输入。对每个输入会终止，允许不同输入各自等待不同的有限展开层数。这正是开头反复出现的那个量词顺序。

再看一个坏递归：

```ocaml
let rec loop n = loop n
```

它的算子是 $\Psi(p) = p$，所以每个偏函数都是不动点，甚至每个全函数也都是不动点。但从最小元出发，

$$
\Psi^k(\bot_{\mathcal{D}}) = \bot_{\mathcal{D}} \quad\text{对所有 }k, \qquad \mu\Psi = \bot_{\mathcal{D}}.
$$

这个最小解忠实地记录了程序没有返回值。随便挑一个全的不动点，会给程序添上它从未计算出来的结果。因此，“这个递归方程有解”本身还不足以说明递归终止。

对上述连续的递归算子，终止问题可以重新写成

$$
\mu\Phi\text{ 是全的} \; \Longleftrightarrow \; \forall n \in \mathbb{N} \; \exists k \in \mathbb{N} \; \bigl(\Phi^k(\bot_{\mathcal{D}})\bigr)(n) \ne \bot.
$$

良基下降描述递归调用之间的关系；信息序描述有限展开已经获得了哪些返回值。阶乘的调用会沿输入下降，同时它的函数近似会沿信息序不断增加。当分析器接受一个良基下降证明时，它证明的正是这个最小不动点在每个合法输入上都有值。

[^diagonal]: 我就说近世代数很坏吧😡（这里实际用的是可计算性理论中的对角线论证；近世代数属于路过挨骂。）

[^totality]: 全性的 $\Pi^{0}_{2}$-完全性可参见 Arnold W. Miller 的 [Lecture notes in Computability Theory](https://people.math.wisc.edu/~awmille1/old/m773-07/cmpthy.pdf)，命题 40.2。

[^jump]: 图灵跳跃与算术层级的对应可参见 Sebastiaan A. Terwijn 的 [Syllabus Computability Theory](https://www.math.ru.nl/~terwijn/teaching/syllabus.pdf#page=46)，第 5.2 节，尤其是命题 5.2.1。

[^finite-syntax]: 对有限语法结构归纳以证明终止的一个标准例子，是 *Software Foundations* 的 [Imp 章节](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html) 中的 `no_whiles_terminating` 练习：不含 `while` 的 Imp 程序总会终止。
    该语言的算术与布尔表达式本身都是全的。

[^structural]: 归纳数据的构造、递归与归纳原则，可参见 *Theorem Proving in Lean 4* 的 [Inductive Types](https://lean-lang.org/theorem_proving_in_lean4/Inductive-Types/)，尤其是第 7.4 节的自然数和第 7.5 节的列表、树。

[^nat-sets]: 自然数后继、归纳集和最小归纳集的集合论构造，可参见 Bob Dumas 与 John E. McCarthy 的 *Transition to Higher Mathematics*，[8.1: The Natural Numbers](https://math.libretexts.org/Bookshelves/Mathematical_Logic_and_Proof/Transition_to_Higher_Mathematics_%28Dumas_and_McCarthy%29/08%253A_New_Page/8.01%253A_New_Page)。

[^orders]: 序关系、良基归纳、字典序与 Ackermann 递归，可参见 Klaus Sutner 的 [Computation and Discrete Mathematics](https://www.cs.cmu.edu/~DMPrimer/pdf/main-fund.pdf)，第 2.2.1 节及第 5.1–5.2 节。
    本文对任意集合上的良基关系采用极小元定义；无无限下降链的反向论证限定在可编码的调用状态上。

[^tarski]: Knaster–Tarski 最小不动点定理及其证明，可参见 Isabelle/HOL 的 [CompleteLattice 理论](https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/library/HOL/HOL-Lattice/CompleteLattice.html) 中的 `Knaster_Tarski`。

[^domains]: 偏函数按扩张关系构成偏序、具有递增信息的上确界，可参见 *Continuous Lattices and Domains* 的[出版社试读章节](https://assets.cambridge.org/052180/3381/sample/0521803381ws.pdf)中关于偏函数的例子。

[^kleene]: 连续算子的有限迭代给出最小不动点，以及这一构造如何用于程序语义，可参见 Cornell CS 4110 的 [Lecture 8: Denotational Semantics Examples](https://www.cs.cornell.edu/courses/cs4110/2020fa/lectures/lecture08.pdf)。
    本文使用保持可数递增链上确界的 $\omega$-连续性表述。
