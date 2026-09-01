---
title: 计算理论视角下的代数效应
pubDate: 2026-9-2
slug: relationship-between-algebra-effect-and-computing
authors:
  - name: Yurin
    url: https://blog.yurin.top/
---

代数效应 (algebraic effect) 是当下 PL 界的常青树之一，也是 FP 小鬼们的最爱，当然目前还有新宠 HoTT. 我们通常从由签名函子 $F$ 生成的自由单子 (free monad) 的角度理解*代数效应*.

## 从签名函子到自由单子

如果我们现在有一个这样的运算

$$
\mathsf{op}:P\rightarrow R
$$

$\mathsf{op}$ 接受一个参数 $p:P$，由外部解释这个请求，再给程序一个回答 $r:R$。如果收到回答后剩余的程序属于 $X$，那么一层尚未解释的操作就是

$$
(p,k)\in P\times(R\rightarrow X).
$$

这里的 $k:R\rightarrow X$ 是续体 (continuation)：它描述“handler 给出某个回答 $r$ 之后，程序接下来做什么”。因此单个操作的签名函子是

$$
F_{\mathsf{op}}X=P\times(R\rightarrow X).
$$

多个操作取和。设签名

$$
\Sigma=\{\mathsf{op}:P_{\mathsf{op}}\rightarrow R_{\mathsf{op}}\},
$$

那么

$$
F_\Sigma X=
\coprod_{\mathsf{op}\in\Sigma}
P_{\mathsf{op}}\times(R_{\mathsf{op}}\rightarrow X).
$$

$F_\Sigma X$ 只描述“一层操作请求”，它本身一般还不是单子。我们需要在操作节点下面继续放操作节点，直到程序返回一个普通值，由此得到 $F_\Sigma$ 上的自由单子 $T_\Sigma$。

### 自由单子

对返回值类型 $A$，自由计算树满足

$$
T_\Sigma A
\cong
A+F_\Sigma(T_\Sigma A),
$$

展开就是

$$
T_\Sigma A
\cong
A+
\coprod_{\mathsf{op}\in\Sigma}
P_{\mathsf{op}}\times
(R_{\mathsf{op}}\rightarrow T_\Sigma A).
$$

也可以把它直接看成一个数据类型：

```haskell
data Free f a where
  Return :: a -> Free f a
  Op     :: f (Free f a) -> Free f a
```

`f` 取具体的签名函子时，`Op` 里装的就是上面 $F_\Sigma$ 的那一层。聪明的读者已经看出，`Free f a` 就是这个不动点：

$$
T_\Sigma A
=
\mu X.\left(A+F_\Sigma X\right).
$$

$\mu X$ 表示取最小不动点。把固定点折回数据类型的构造映射记作

$$
\mathsf{in}_A:
A+F_\Sigma(T_\Sigma A)
\longrightarrow T_\Sigma A,
$$

那么两个构造器分别来自左右两支：

$$
\begin{aligned}
\mathsf{Return}
  &=\mathsf{in}_A\circ\mathsf{inl},\\
\mathsf{Op}
  &=\mathsf{in}_A\circ\mathsf{inr}.
\end{aligned}
$$

`Return` 是递归不再向下展开的锚点，把普通值嵌进计算树；`Op` 则增加一层请求，并在每个回答对应的续体里继续递归。因此 `Return` 是自由单子的 unit：

$$
\eta_A=\mathsf{Return}:A\longrightarrow T_\Sigma A.
$$

这里选择最小不动点，所以得到的是良基请求树：沿任何一条续体路径都不能无限向下展开。若要表示一般递归和发散，还要再加入 partiality、domain-theoretic least fixed point，或采用适合无限行为的余归纳语义；一个普通的 `Free F` 不会凭空包含这些东西。

于是，`Return` 表示计算已经完成，`Op` 表示程序把请求交给外部，并把收到回答后的剩余计算保存在续体里。因此

$$
\mathsf{return}(a)=\mathsf{Return}(a),
$$

而一次操作调用是

$$
\mathsf{perform}\ \mathsf{op}(p)
=
\mathsf{Op}(\mathsf{op},p,
\lambda r.\mathsf{Return}(r)).
$$

顺序组合，也就是 bind，则把后续函数接到树的每一个返回叶子上：

$$
\begin{aligned}
\mathsf{Return}(a)\mathbin{\gg=}f
  &=f(a),\\
\mathsf{Op}(\mathsf{op},p,k)\mathbin{\gg=}f
  &=\mathsf{Op}(\mathsf{op},p,
      \lambda r.k(r)\mathbin{\gg=}f).
\end{aligned}
$$

bind 不会擅自解释操作，只会把 $f$ 接到请求之后。因此，后一个请求可以依赖前一个请求的回答。

由这个定义可以推出三条单子律：

$$
\begin{aligned}
\mathsf{return}(a)\mathbin{\gg=}f
  &=f(a),\\
m\mathbin{\gg=}\mathsf{return}
  &=m,\\
(m\mathbin{\gg=}f)\mathbin{\gg=}g
  &=m\mathbin{\gg=}(
      \lambda x.f(x)\mathbin{\gg=}g).
\end{aligned}
$$

第一条是左单位律，说明 `return a` 对后续函数 $f$ 完全透明；

第二条是右单位律，说明把树的每个返回叶子重新包成 `return`，最后仍是原来的树；

第三条是结合律，保证长串 bind 可以安全地重新分组。

第三条尤其不是交换律。我们只能把

$$
(m\mathbin{\gg=}f)\mathbin{\gg=}g
$$

重新加括号，不能把 $f$ 和 $g$ 对调；effect 的先后顺序仍然可能改变结果。抛开玩笑看，这两条单位律加一条结合律正是 monoid 的形状，也对应“monad 是 endofunctor composition 下的 monoid”那句著名但初看不说人话的定义。

所以自由单子只记录程序的请求结构和控制流，不决定请求的真实含义。

### handler 执行了 `k args`

在 direct style 里，我们容易把

```ocaml
let x = perform (op p) in
rest x
```

理解为“`perform` 执行后返回一个 `x`”。但 CPS 下没有这样的直接返回。它更接近

```ocaml
perform_cps op p (fun x -> rest x)
```

也就是把请求参数 $p$ 和当前续体 $k$ 一起交给最近的 handler。暂时略去 handler 的 `return` 子句和外层续体，一个只保留操作核心结构的 CPS 求值器可以写成：

```ocaml
let rec eval term h k =
  match term with
  | Return v ->
      k v
  | Let (m, f) ->
      eval m h (fun x -> eval (f x) h k)
  | Perform (op, p) ->
      handle_op h op p k
```

最后一行没有调用 $k$。`perform` 所做的是把控制权、参数 $p$ 和“剩下的程序” $k$ 一起移交给 handler。之后是否继续，是 handler 的决定：

```ocaml
let handle_once p k =
  k (answer p)                              (* 恢复一次 *)

let handle_abort _p _k =
  abort ()                                  (* 不恢复 *)

let handle_many p k =
  combine (k (left p)) (k (right p))        (* 恢复多次 *)
```

若 $\mathsf{op}:P\rightarrow R$，那么这里传给 $k$ 的 `answer` 或 `args` 必须属于 $R$；多个回答参数可以先打成一个 tuple。所谓“`perform op p` 返回了 $r$”，只是 handler 执行 `k r` 后在 direct style 里的表象。

把 handler 写成通常的语法：

```ocaml
handle e with
| return x -> e_return
| op p k   -> e_op
```

它的关键操作语义是

$$
\begin{aligned}
&\mathsf{handle}\ E[\mathsf{perform}\ \mathsf{op}(v)]\;
  \mathsf{with}\ H\\
&\qquad\longrightarrow
e_{\mathsf{op}}
\left[
v/q,
(\lambda r.
  \mathsf{handle}\ E[\mathsf{return}\ r]\;
  \mathsf{with}\ H)/k
\right].
\end{aligned}
$$

这里 $E$ 是从 `perform` 到最近 handler 之间剩余的求值上下文，$q$ 是操作子句绑定的参数变量，$v$ 是实际请求参数。因此 handler 实际拿到的续体就是

$$
k=\lambda r.
\mathsf{handle}\ E[\mathsf{return}\ r]\;
\mathsf{with}\ H.
$$

于是操作子句里的 `k args` 真正做的是：把 handler 产生的回答 `args` 塞回请求点，并从那里继续执行 $E$。这里重新安装了 $H$，所以这是 deep handler；恢复后的下一次同类操作仍会被同一个 handler 捕获。

从自由树的角度看，同一件事写成 fold：

$$
\begin{aligned}
\mathcal H(\mathsf{Return}(a))
  &=h_{\mathsf{return}}(a),\\
\mathcal H(\mathsf{Op}(\mathsf{op},p,k))
  &=h_{\mathsf{op}}(
      p,\lambda r.\mathcal H(k(r))).
\end{aligned}
$$

$h_{\mathsf{op}}$ 收到的第二个参数就是已经递归安装 handler 的续体。它调用零次、一次还是多次，分别得到异常/提前返回、普通请求-回答和非确定搜索等不同控制行为。

## 神谕机

万恶的哥德尔和并不 naive 的近世数学告诉我们，世界上没有完美的机器.

在光明到打了两次世界大战的 20 世纪上半叶，Gödel 讨论了形式系统能证明什么，Turing 讨论了机器能计算什么；通过自指和对角化给出了公理系统和计算机的能力边界。

### 什么叫“可计算”

程序**并不总会**返回，所以它自然表示一个**部分函数**：

$$
\varphi_P:\{0,1\}^*\rightharpoonup\{0,1\}^*.
$$

$\{0,1\}^*$ 是有限二进制字符串，也可以换成自然数编码。这里不用 $\Sigma^*$，是为了避免和前文的 effect signature $\Sigma$ 混淆。若程序 $P$ 在输入 $x$ 上停机并返回 $y$，记作

$$
\varphi_P(x)\downarrow=y;
$$

若它永远运行，则记作 $\varphi_P(x)\uparrow$，此时函数在 $x$ 上没有定义。所谓“可计算函数”，通常就是存在某个程序或图灵机实现的部分函数。

Church–Turing thesis 认为，任何机械、有效的计算过程都可以由图灵机表达。lambda calculus、一般递归函数、register machine 等模型虽然长得不同，却得到同一类部分可计算函数。

### 判定、识别与发散

一个 yes/no 问题可以表示成语言或集合

$$
A\subseteq\{0,1\}^*.
$$

它的特征函数为

$$
\chi_A(x)=
\begin{cases}
\mathsf{true},&x\in A,\\
\mathsf{false},&x\notin A.
\end{cases}
$$

常见层次要分开：

| 性质                      | 机器在 $x\in A$ 时 | 机器在 $x\notin A$ 时 |
| ----------------------- | -------------- | ----------------- |
| 可判定 decidable           | 停机并回答 `true`   | 停机并回答 `false`     |
| 可识别 recognizable / c.e. | 最终停机并接受        | 可以拒绝，也可以永远运行      |

若连第二行都做不到——不存在任何机器恰好在 $A$ 中所有输入上停机接受——就称 $A$ **不可识别**。

$A$ 可判定，当且仅当 $A$ 和补集 $\overline A$ 都可识别。这里最要紧的差别是：没有看到结果，不等于结果是 `false`；程序可能只是还没有停机。

### 对角化

上面的“没有统一判定器”不是靠逐个检查机器得到的，而是靠对角化：假设一个系统能够完整描述或判定所有对象，再把这个系统自己的描述喂回给它，构造一个专门否定其答案的对象。

#### Turing 的停机问题

把程序及其输入编码成字符串，定义

$$
K=\{\langle P,x\rangle\mid\varphi_P(x)\downarrow\}.
$$

$K$ 可识别：直接模拟 $P(x)$，它停机时接受即可。但 $K$ 不可判定。假设存在一个总函数

```ocaml
halts : code -> code -> bool
```

能正确判断任意程序是否停机，就可以构造

```ocaml
let diagonal (p : code) =
  if halts p p then
    loop ()
  else
    ()
```

令 $d$ 是 `diagonal` 自身的程序编码，再运行 `diagonal d`：若 `halts d d` 回答停机，`diagonal d` 就故意循环；若回答不停机，它反而立即返回。两个答案都会否定自己，因此这样的 `halts` 不存在。

很多具体程序当然可以证明终止或发散。此处的结论是不存在一个对**所有**程序都停机并给出正确答案的统一判定器。

Rice theorem 把这个现象推广到程序计算出的部分函数：任何非平凡的外延语义性质，都不存在适用于所有程序的判定算法。

#### What do Gödel and Turing say?

Gödel 第一不完备定理大致说：任何一致、可有效公理化并且足以表达初等算术的形式理论都是不完备的，存在它既不能证明也不能否证的句子。若再要求理论对标准自然数模型足够可靠，才可以把相应结论表述成“存在真但不可证的算术命题”。第二不完备定理进一步说明，在通常的可推导性条件下，一致的理论不能在内部证明自身的一致性。

Turing 的结论则是：不存在判定所有程序停机性的算法。

一个讲证明，一个讲计算。二者可以通过编码联系起来，也共享对角化结构，它们否定了全能、统一、内部自证的完美系统。

> 在这个世界上，根本就没有神。    ——刹那·F·清英

### 相对可计算性

不可计算性总是相对于机器当前拥有的基本操作而言。若给机器增加一个集合 $A$ 的成员查询

$$
\mathsf{ask}_A:\mathbb N\rightarrow\mathsf{Bool},
$$

并规定它一步返回 $\chi_A(n)$，就得到带 $A$ 神谕的机器 $M^A$。若机器借助 $A$ 能判定问题 $B$，记作

$$
B\leq_T A.
$$

若 $A$ 本来可计算，神谕查询可以被普通程序内联，计算能力并没有增加；若 $A$ 不可计算，它可能让原本不可判定的问题变得可判定。但层级不会因此封顶。相对于 $A$ 的停机集合

$$
A'=\{\langle P,x\rangle\mid\varphi_P^A(x)\downarrow\}
$$

仍然不能由 $A$ 自己判定，这就是 Turing jump。

从更宽的意义看，任何 effect handler $H$ 都给程序一个相对环境：

$$
\llbracket P\rrbracket^H,
\qquad
\mathcal C^H.
$$

经典集合神谕只是无状态、一次问答的特例。`Read`、`State`、`IO` 或非确定 handler 也都可以相对化出各自的问题空间，只是它们可能依赖历史、交互协议或续体恢复方式，不能不加说明地直接套用图灵度。

#### pure 核心是破损核心

实际上我们并不是先拿到一台能力完整的机器，再凭空往上添加 effect；语言设计者先把一部分转移规则从核心机器里拆出去，只留下所谓 pure core。剔除的是**环境转移**——读写、状态、时钟、随机、控制转移——而不是计算能力；$\lambda$ 演算这样的纯核心不带任何 effect 也天生 Turing complete，它观察与交互的能力被限制，但是对已给定数据的计算力保留。

若完整机器的转移可以粗略分成

$$
\delta_{\mathsf{full}}
=
\delta_{\mathsf{core}}
\uplus
\delta_{\mathsf{env}},
$$

pure 语言只保留 $\delta_{\mathsf{core}}$。文件读取、状态更新、时钟、随机选择甚至某些控制转移都从核心转移表中被挖掉，留下签名为

$$
\mathsf{op}:P_{\mathsf{op}}\rightarrow R_{\mathsf{op}}
$$

的洞。程序走到这个洞时，核心机器自己没有产生 $r:R_{\mathsf{op}}$ 的规则，只能把参数和续体交出去：

```ocaml
handle_op h op p k
```

以及 handler 随后的 `k r`。没有 handler 时，机器停在一个开放的 `Op (op, p, k)` 节点；handler 就是给转移表里的洞补上解释。会丢弃或复制续体的 handler 更一般：它不一定只返回一个 $r$，还可以调用 $k$ 零次或多次。

> 注意: pure core 即使保留一般递归，也可以对**已经作为普通值交给它的数据**保持 Turing complete.

#### 为什么 effect 会自然地相对化问题空间

相对问题空间几乎不证自明。一个计算模型能解决的问题，就是某个程序按其转移规则运行时能对所有输入正确判定的问题。pure core 对应基础类 $\mathcal C_{\mathsf{core}}$；固定 handler $H$，就是把一组缺失转移装回核心机，得到 $M_{\mathsf{core}}^H$，于是

$$
\mathcal C_{\mathsf{core}}^H=
\left\{
B\subseteq\{0,1\}^*
\ \middle|\
\exists P.\ \forall x.\
\llbracket P(x)\rrbracket^H=\chi_B(x)
\right\}.
$$

$\mathcal C_{\mathsf{core}}^H$ 只是所有程序在补完后的机器上所能判定的问题集合。改变 handler，就是用不同方式补机器的洞，自然也会改变机器能观察的信息、允许的转移和可解问题；不需要额外假设一条“effect 可以相对化”的公理。下文简写成 $\mathcal C^H$。

不过，只有 effect signature 还不够。签名只规定洞的形状，handler 才规定如何填洞。因此 $\mathsf{Read}$ 本身严格说对应的是一族

$$
\{\mathcal C^{H_s}\}_{s\in\mathsf{Stream}},
$$

其中字符流 $s$ 给出一个按顺序回答的 `Read` handler $H_s$。程序可以计算一个依赖环境的函数

$$
\llbracket P(x)\rrbracket^{H_s}=f(x,s).
$$

例如“返回输入流的首字符”之所以需要 `Read`，正因为 pure core 被刻意设计成既没有 `Read` 转移，也没有把 $s$ 当作普通参数：核心程序看不见 $s$，不可能对两个首字符不同的流给出不同答案。handler 把被删掉的观察能力装回来后，这件事只需一次请求。[^1]

### 一个子集

在上面 capability-deficient core 的基础上，我们再定义一个足够简单的受限语言 $\mathrm{AE}_0$。

我们假设一门 **Scheme-shaped** 的语言，我们要求其没有 `define`、`lambda`、`letrec`、named let、`set!` 和 `call/cc`；不能写递归或自己制造无限循环。程序只有字面值、总的 primitive、`if`、顺序 `let`、`return`、`perform` 和 `handle`。handler 里拿到的 $k$ 是唯一特殊的可调用对象。

一个纯计算看起来就是普通 Scheme：

```scheme
(let ((x (+ 20 22)))
  (return x))
```

这里的 `let` 不是宿主 Scheme 的普通值绑定，而是带顺序求值的 monadic let。右侧若产生请求，拿到 handler 的回答后才会执行 body。例如先问一个问题，再根据答案决定是否输出：

```scheme
(let ((answer (perform ask 4)))
  (if answer
      (let ((_ (perform print "yes")))
        (return "yes"))
      (return "no")))
```

effect 名 `ask`、`print` 都来自一个有限签名。可以把

```scheme
(perform ask 4)
```

读成前文的

$$
\mathsf{Op}(\mathsf{ask},4,
  \lambda answer.\mathsf{Return}(answer)).
$$

Handler 也直接写成 Scheme 形状。下面的 handler 用 `even?` 回答所有 `ask`，并通过 `k` 恢复计算：

```scheme
(handle
  (let ((a (perform ask 4)))
    (let ((b (perform ask 9)))
      (return (and a (not b)))))

  (return (x)
    (return x))

  (ask (q k)
    (k (even? q))))
```

第一次请求得到 `#t`，第二次得到 `#f`，整个程序最后返回 `#t`。关键仍然是 handler 主动调用 `(k (even? q))`；`perform` 自己没有返回答案。

不调用和调用多次也保持 Scheme 的样子：

```scheme
;; 丢弃 k：后面的计算不再执行
(fail (message k)
  (return (list 'error message)))

;; 调用 k 两次：同一个续体产生两个分支
(choose (_ k)
  (append (k #t) (k #f)))
```

把程序记为 $P$，执行它的机器记为 $M(P)$，基础问题类记为 $\mathcal C$；装上 handler $H$ 后得到 $\llbracket P\rrbracket^H$ 和 $\mathcal C^H$。为了让下一节的精确分析确实是算法，我们还要求 effect signature 有限、每个回答类型有限可枚举，并且 handler 自身也不能引入发散。


#### Handler 写在哪种语言里，对 $\mathcal C^H$ 很重要

handler 自己写在哪种语言里？这直接决定 $\mathcal C^H$ 相对 $\mathcal C$ 的增益。

若核心已经 Turing complete（如后文的 $\mathrm{AE}_\mu$），而 handler $H$ 本身可计算——存在普通程序实现它的 fold——那么 $\mathcal C^H=\mathcal C$。这正是神谕一节“若 $A$ 本来可计算，查询可以被内联”的效应版：解释器走到 `Op` 节点时，把 handler 代码就地调用来填洞；mutishot handler 无非把 $k$ 多跑几次，丢弃续体无非删掉一段计算，都可以被普通程序模拟。装一个可计算 handler，等于把一段普通代码接进程序，一分不涨。

若核心像 $\mathrm{AE}_0$ 一样刻意没有递归，可计算的 handler 也能提升 $\mathcal C^H$，增益有两个来源：新装回的**转移**改变机器能观察什么；handler 代码自身的**计算力**（若允许用比核心更强的语言书写）改变机器能算什么。


### 更强的语言

但是我们往往需要一种更强的语言来解决实际问题。于是把一般递归、高阶函数、递归数据和开放模块逐项装回来，得到接近普通通用语言的 $\mathrm{AE}_\mu$。它的 pure core 重新达到 Turing complete，环境 capability 仍然通过 effect 从核心外部接入。

从 $\mathrm{AE}_0$ 到 $\mathrm{AE}_\mu$，`perform` 产生请求、handler 接管续体的动态语义没有变化。变化的是编译器能否在运行前完整预测程序行为。因此 effect row 不是“语言只要 effectful 就必须拥有”的构造；一门解释器完全可以只执行 `perform`/handler，而不做任何静态 effect tracking。

### Effect row 不是 effectful 的前提

#### 子集语言中可以精确收集

对 $\mathrm{AE}_0$ 的规范化请求树，可以精确定义其中可达的操作：

$$
\begin{aligned}
\mathsf{Ops}(\mathsf{Return}(v))
  &=\varnothing,\\
\mathsf{Ops}(\mathsf{Op}(\mathsf{op},p,k))
  &=\{\mathsf{op}\}\cup
    \bigcup_{r\in R_{\mathsf{op}}}
      \mathsf{Ops}(k(r)).
\end{aligned}
$$

因为树有限、每种回答也有限，这个遍历一定结束，而且得到的是语义上精确的集合。例如

```scheme
(if #f
    (perform ask 0)
    (return '()))
```

会先归约成 `(return '())`，所以不会收集到 `ask`。若安装了具体 handler，则先用 handler fold 请求树，再收集处理后仍向外可见的操作；不恢复续体的 handler 会真正删掉续体后不可达的 effect。

事实上还可以更贪心。请求树有限、handler 子句停机，意味着整个 fold 的调用图都是有限的，宿主机器可以把它完整枚举出来。因此能被精确收集的不只是操作集合，还有**恢复协议 (resume protocol)**：

- 在每个 $\mathsf{Op}$ 节点上，handler 调用 $k$ 零次、一次还是多次；
- 每次调用喂入的回答及其顺序；
- 最终返回值，以及向外逃逸的未处理操作。

也就是说，对 $\mathrm{AE}_0$ 做 effect 分析，得到的不只是一行 sound 且 complete 的 row，还可以得到程序与 handler 的完整交互轨迹——`fail` 丢弃续体、`choose` 复制续体这类控制行为，在运行之前就全部可见。唯一的假设是 handler 子句停机；一旦允许 handler 发散，分析立刻撞上（元语言的）停机问题，我们将在下一节讨论。

#### 效应收集器是相对 $\mathrm{AE}_0$ 的 Oracle

我们不妨把可达性查询直接做成 effect：

```scheme
;; 签名：询问一棵有限请求树的语义信息
(reach   : (code, op) -> bool)   ;; 这棵请求树会到达 op 吗
(ops-of  : code -> opset)        ;; 可达操作的完整集合
```

$\mathrm{AE}_0$ 自己写不出这两个 handler：实现 `reach` 要递归遍历任意大小的请求树，而 $\mathrm{AE}_0$ 没有递归——total 语言无法自解释，否则对角化当场爆炸。但宿主语言（普通图灵机，或者后文的 $\mathrm{AE}_\mu$）写得出来：handler 就是上面的 $\mathsf{Ops}$ 遍历，回答永远正确。

$\mathrm{AE}_0$ 的 Turing jump 落在普通可计算性之内，跑解释器的那台机器就是 Oracle。

#### 图灵完备之后遇到停机障碍

但这个办法依赖 $\mathrm{AE}_0$ 必定终止。“某个 effect 是否可达”并不完全是程序所计算部分函数的外延性质，因此不必硬套 Rice theorem；直接从停机问题归约即可:

给语言加入一般递归后，假设仍有一个总算法能精确判断任意程序是否可能到达 `ask`。对任意 $P$ 和输入 $x$ 构造

```scheme
(let ((_ (run p x)))
  (perform ask 0))
```

那么

$$
\mathsf{ask}\text{ 可达}
\quad\Longleftrightarrow\quad
P(x)\text{ 停机}.
$$

这个 effect 分析器就能判定停机问题，因此普通机器上不可能存在。现实 effect system 只能在可判定性和精度之间选择：通常推导一个 sound 的保守 row，使实际 effect 不会超出它，但允许 row 包含死分支里永远不会发生的 effect。常量折叠、路径敏感分析、SMT 和 refinement type 可以消掉更多假阳性，却不可能对所有图灵完备程序同时做到 sound、complete 且可判定。

#### 如果编译器自己有 oracle

不可判定性限制的是普通可计算的分析器，不是 effect semantics。固定运行环境 $H$ 和分析边界，假设编译器可以请求一个精确的可达性 oracle：

$$
\mathsf{Reach}^H(P,\mathsf{op})=
\begin{cases}
\mathsf{true},&P\text{ 在 }H\text{ 下可能到达 }\mathsf{op},\\
\mathsf{false},&\text{否则}.
\end{cases}
$$

对有限签名 $\Sigma$，它就能直接计算

$$
\mathsf{Eff}^H(P)=
\{\mathsf{op}\in\Sigma
\mid\mathsf{Reach}^H(P,\mathsf{op})=\mathsf{true}\}.
$$

这时 row 可以作为编译器生成的结果，甚至完全不出现在 surface language 中。用户写 Koka 还是 Kola 都不必亲手写 effect row；只要那台编译机真的拥有所需的 oracle，它就能替用户算出来。对 $\mathrm{AE}_0$，这台 oracle 甚至不需要假设：普通编译器就是它的 $\mathsf{Reach}$ 神谕（见前文的真 oracle 小节）。

这里要注意，不是任意 oracle 都够用。程序相对于 handler/oracle $H$ 运行时，它自己的停机与可达性问题通常不由 $H$ 本身判定，而需要相应的 jump $H'$，或者直接提供 $\mathsf{Reach}^H$。停机神谕也不能自动判定带同一个停机神谕程序的停机性。

如果读者此时手边恰好有反德西特空间或者裸奇点，不妨进行一些尝试 :-)

## 参考阅读

### 代数效应与 handler

- Plotkin, G. D. & Power, J. *Notions of Computation Determine Monads*. FoSSaCS 2002.（签名函子与代数运算的范畴语义基础；同系列还有 *Adequacy for Algebraic Effects*, FoSSaCS 2001。）
- Plotkin, G. D. & Pretnar, M. *Handlers of Algebraic Effects*. ESOP 2009；完整版 *Handling Algebraic Effects*, Logical Methods in Computer Science 9(4), 2013.（handler 的原始定义。）
- Pretnar, M. *An Introduction to Algebraic Effects and Handlers*. Electronic Notes in Theoretical Computer Science 319 (MFPS 2015), pp. 19–35.（最好的入门综述；本文的 deep handler 规则即出于此文。）
- Bauer, A. & Pretnar, M. *An Effect System for Algebraic Effects and Handlers*. CALCO 2013.（Eff 语言与 effect 推断。）

### 自由单子与效应的语义

- Moggi, E. *Notions of Computation and Monads*. Information and Computation 93(1), 1991.（用单子建模计算效应的起点。）
- Swierstra, W. *Data Types à la Carte*. Journal of Functional Programming 18(4), 2008.（签名函子、余积与自由单子的编程视角。）
- Capretta, V. *General Recursion via Coinductive Types*. Theoretical Computer Science 338, 2005.（partiality monad：自由单子只有良基树，一般递归与发散要靠余归纳补。）

### handler 走进真实语言

- Leijen, D. *Koka: Programming with Row-Polymorphic Effect Types*. MSR-TR-2014-39.（row polymorphic effect type 的代表实现。）
- Lindley, S., McBride, C. & McLaughlin, C. *Do Be Do Be Do*. POPL 2017.（Frank：handler 作为一等公民。）

### 可计算性

- Cutland, N. *Computability*. Cambridge University Press, 1980.（最平易近人的系统教材；判定/识别、停机、Rice、相对化全覆盖。）
- Soare, R. I. *Turing Computability: Theory and Applications*. Springer, 2016.（相对可计算性、Turing jump 与度结构的现代教材。）
- Rogers, H. *Theory of Recursive Functions and Effective Computability*. McGraw-Hill, 1967.（经典参考书。）
- Sipser, M. *Introduction to the Theory of Computation*. 3rd ed., Cengage Learning, 2013.（对角化与停机问题的标准入门处理。）
- Smith, P. *An Introduction to Gödel's Theorems*. 2nd ed., Cambridge University Press, 2013.（两个不完备定理的仔细陈述，包括“真而不可证”为何需要超出一致性的可靠性。）

[^1]: 这里的增强首先是信息接口上的相对化，不一定提高 Turing degree。若整个有限流本来就作为普通输入传给核心机，`Read` 可以被普通函数模拟，只改变信息的提供方式和时序；若 $s$ 是固定的不可计算无限流，它才可能真正提升经典可计算能力。对 `State`、并发或非确定性，还需要把初始状态、调度策略和成功条件一起放进 $H$，问题空间才定义完整。
