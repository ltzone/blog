---
title: Completeness of FOL
url: pl-fol
date: 2020-04-28 14:04:23
tags: 
- Programming Language

categories: 
- Courses

---

Week 9 of 2020 Spring

<!--more-->




## Assigment Review

### Understanding Syntax Tree

1. If `X` and `Y` are distinct program variables, `E1` and `E2` are integer expressions, `P` is an assertion, then 
  `P [X |-> E1] [Y |-> E2]` is not equivalent to `P [Y |-> E2] [X |-> E1]`, but is equivalent to `P [X |-> E1] [Y |-> (E2 [X |-> E1])]`

2. If `X` is a program variables, `x` is a logical variable, `P` is an
    assertion, then `P` is a stronger assertion than  `EXISTS x, P [X |-> x]`.
  - If `x` freely occur in `P`. E.G. `P` is `{[X]} = x + 1`, the substitution becomes `EXISTS x, {[x]} = x + 1`.  The later is stronger because nothing is stronger than False. The proposition fails because we let `x` freely occur in `P`.
  - But with constraint of not freely-occur, the proposition holds.
  - For this problem, 1 and 2 are both considered to be right.

### Weakest Preconditions

1. For any assertion `P`, program variable `X` and integer expression `E`, ` P [X |-> E] ` is a weakest precondition of `X ::= E` and `P`. 正确，back_asgn_rule定义了最弱前条件。

2. For any assertion `P`, logical variable `x`, program variable `X` and integer expression `E`, if `x` does not freely occur in `P`, then ` P ` is a weakest precondition of `X ::= E` and ` EXISTS x, P [X |-> x] AND {[ X ]} = {[ E [X |-> x] ]}`. 探讨fwd_asgn_rule。后条件一定是P和赋值语句的最强后条件。问题是：如果后条件是前条件的最强后条件，前条件是不是前条件的最弱后条件？（不一定）。
  考虑这样一个例子：由于没有被P描述的额外状态的存在，由最强后条件生成的最弱前条件还要强一些，我们只需构造如下图所示的情形：
  ```
  { wp of strongest post P (Q)}
    [ ] [ ] [ ] [ ] := {P} [ ]
    |   |   |   |           |
    V   V   V   V           |
    [ ] [ ]   [ ]   <-------- := {Q}
  ```
  Let `P` be `{[X]} = 1`, `E` be `0`. Then strongest post condition is `EXISTS x, {[x]} = 1 AND {[X]} = 0`, which is equivalent to `{[X]} = 0`. Then the weakest precondition of `{[X]} = 0` and `X := 0` is (by backward assignment rule) `{[0]} = 0` or `True`.

3. If `P` is a weakest precondition of `c` and `Q`, and `P` is equivalent to `P'`, then `P'` is also a weakest precondition of `c` and `Q`. (Here, we say that `P` and `P'` are equivalent when: for any interpretation `J`, `J |== P` if and only if `J |== P'`.


4. For any assertions `P`, `Q`, any boolean expression `b` and any loop body `c`, if `P` is a weakest precondition of `While b Do c EndWhile` and `Q`, and `P` is also a weakest precondition of `While b Do c EndWhile` and ` P AND NOT {[ b ]} `.


> Recall
> For any assertions `P` and `Q`, any boolean expression `b` and any loop body `c`, if `P` is a weakest precondition of `While b Do c EndWhile` and `Q`, then `P AND {[b]}` is a weakest precondition of `c` and `P`.
> ```
> {         P           }
>   [A] [ ] [ ] [ ] [ ]
>    |   |   |   |   | 
>  b |   |   |   |   | 
>    |   |   |   |   | 
>  c |   |   |   |   |   While b Do c EndWhile
>   [B]  |   |   |   | 
>    |   |   |   |   | 
>    |   |   |   |   | 
>    ----|   |   |---- 
>        V   V   V 
>   [F] [C] [ ] [ ] [G] <-------- := {Q}
> ```
> 显然，`[B]`一定符合P,根据我们证明过的引理，`[C]`一定符合`P AND ~ b`. 即任何状态，如果符合`P`, 那么执行循环能够到达的一定是`P AND ~ b`.


> A more concrete Example
> 
> ```
>     [A]     [F]     [J]
>      |       |       |   test b
>      |       |       |   c
>     [B] [D] [G] [H] [K]
>      |   |   |   |   |   test 
>      |   |   |   |   |   c
>     [C] [E]  ---[I] [L]
>      |   |       |   |             While b Do c EndWhile
>      |   |       |   |
>      ----|       |----
>          |       |       ~ b
>     [X] [M]     [N] [Y]
> ```
> 
> if `Q = {X, M, N, Y}`
> then `P = {A, B, C, D, E, F, G, H, I, J, K, L, M, N},`
> `P AND {[b]} = {A, B, C, D, E, F, G, H, I, J, K, L}`
> `P AND ~ {[b]} = {M, N}`.


## Review

In a logic, a statement is _provable_ (可证) if we can derive it from proof rules. A statement is _valid_ (有效) if it is always true according a semantic definition. We say a logic is _sound_ (可靠) if all provable statements are valid. We say a logic is _complete_ (完全) if all valid statements are provable.  We have proved that our Hoare logic is sound and/or complete if the underlying logic for assertion derivation is sound and/or complete.

## FOL Completeness: The definition

在对一阶逻辑做证明时，我们要对完全性做加强。

```Coq
Definition complete: Prop :=
  forall P: prop, |== P -> |-- P.
```
上面的定义称为弱完全性。

如果存在GAMMA中的有穷集（命题集合），合在一起，

语义后承

可以把语义后承看作有效的一种推广。


定义强完全性，如果强完全性成立，只需令Gamma为空，那么弱完全性可推出。
```Coq
Definition strongly_complete: Prop :=
  forall Gamma P,
    Gamma |= P -> Gamma |-- P.
```

## Important FOL theorems

我们只需证明强完全性，在证明过程中，我们会用到一些一阶逻辑的导出规则。暂时跳过。

## Proof By Contraposition: Satisfiability and Consistency

证明第一步，将强完全性规约到一致性和可满足性。


### Satisfiability

一致性：不能推出False。Gamma中是否能选取有穷多个，imply后者，不能推出False。即这个命题不能可证。
```Coq
Definition consistent (Gamma: prop -> Prop): Prop :=
  ~ (Gamma |-- PFalse).
```

展开consistent的语义，我们有如下等价引理。
```Coq
Lemma not_derive_spec: forall Gamma P,
  ~ (Gamma |-- P) <-> consistent (Gamma:; (NOT P)).
```
**Proof Sketch**
`Gamma:; (NOT P)` consistent
$\iff$ `Gamma:; (NOT P) |- False` is wrong
$\iff$ `Gamma |- (NOT P) -> False` is wrong
$\iff$ `Gamma |- P` is wrong.

### Consistency

一个命题集合可满足，存在一个解释，能同时满足集合中的所有命题。

```Coq
Definition satisfiable (Gamma: prop -> Prop): Prop :=
  exists J, forall P, Gamma P -> J |== P.
```

性质：和语义后承的关系

```Coq
Lemma not_entail_spec: forall Gamma P,
  ~ (Gamma |= P) <-> satisfiable (Gamma:; (NOT P)).
```

`satisfiable (Gamma:; (NOT P))` 有一个解释，使Gamma为真，P为假，那找到就是找到了。


### Proof
用反证法说明：如果我们要证明强完全性，只需证明任何一致集可满足。
```Coq
Lemma proof_by_contraposition:
  (forall Gamma, consistent Gamma -> satisfiable Gamma) ->
  strongly_complete.
Proof.
  intros.
  unfold strongly_complete.
  intros Gamma P.
  assert (~ (Gamma |-- P) -> ~ (Gamma |= P)); [| tauto].
  intros.
  apply not_derive_spec in H0.
  apply not_entail_spec.
  apply H.
  exact H0.
Qed.
```

如何证明任意一致集可满足？找到一个解释，这是一个构造性的证明。

我们的构造分为两步，第一步称为极大一致集构造，第二部称为典范模型的构造及证明。

## Henkin Style Proof and Maximal Consistent Set

- 一个集合是极大一致的 iff 它是一致（推不出False）的，加上任何其他命题都不一致。
- 一个集合是witnessed iff 对于一阶逻辑的存在命题，我们总能找到目击者命题。即存在命题不能凭空存在。


我们证明目标：对任意一个一致集，我们总能将它扩充成为一个极大一致、witnessed的集合。

进一步，我们要证明极大一致的witnessed集合可满足。

### Lindenbaum Lemma: Constructing MCS with witness

构造witnessed的极大一致集（MCS maximal consistent set）。

#### Step 1.
对Gamma集合中的每一个命题中的变元做重命名。可能Gamma已经有无穷变元了，占满了，我们希望腾出无穷多个自由变元供后续使用。
我们现在要求，$\Gamma \Rightarrow \Gamma_0$。$\Gamma_0$中编号为偶数的自由变元都没有被使用过，显然，$\Gamma_0$的可满足性、一致性都是维持的。

#### Step 2.
语法树构造的，因此 first order propositions are countable. 我们肯定有 $P_1,P_2,\ldots$

我们构造一列$\Gamma$. 放入思想：不断增加，一个个加进去，一致的加进去，不一致的不加。保证这一列每一个都是一致的。

最后的结果是一个无穷并。显然，每一个Gamma是一致的。无穷并是一致的吗？

是的，不然如果并集是不一致的，那么我们从并集中取出有穷多个命题，导致不一致。找到加入时对应的Gamma，那说明当时的构造不符合加入的规范。

上面的论述只说明了“极大一致”，下面我们还要给witness打补丁。

Specifically, for every natural number n, we construct Gamma(n+1) from Gamma(n) according to the following rules:
- case a. if Gamma(n):; P(n+1) is consistent and P(n+1) has a form of EXISTS x. Q, then let Gamma(n+1) be Gamma(n) :; Q[x ⟼ y] :; P(n+1) in which y is a variable that does not occur in Gamma(n) or P(n+1). 命题具有存在的形式，我们希望找到一个$y$使得，我们不仅加入了存在形式的命题，也加入了witness形式的命题，即一次性加两个命题。这样的$y$能不能找到呢？我们要找在Gamma和P中的变元从来没有自由出现过。
- case b. if Gamma(n):; P(n+1) is consistent and P(n+1) does not have a form of EXISTS x. Q, then let Gamma(n+1) be Gamma(n):; P(n+1). 一致的，但命题不是存在的形式，加进去就好
- case c. if Gamma(n):; P(n+1) is inconsistent, then let Gamma(n+1) be Gamma(n). 不一致的不加，保持原来一样


我们还需要对case a情形中加入的witness命题是否一致进行证明。
**Proof Sketch.**

Assumption: 
- `Gamma(n) :; EXISTS x, Q |-/- False`
- y does not freely occur in `Gamma(n):; EXISTS x, Q`

RoadMap
- `Gamma(n) :; EXISTS x, Q |-/- False`
- `Gamma(n) :; EXISTS x, Q |-/- NOT (EXISTS x. Q)`
- `Gamma(n) :; EXISTS x, Q |-/- FORALL x. NOT Q`
- `Gamma(n) :; EXISTS x, Q |-/- FORALL y. (Q [x |-> y] --> False)`
- `Gamma(n) :; EXISTS x, Q |-/- Q [x |-> y] --> False (by not free)`
- `Gamma(n) :; Q [x |-> y] :; EXISTS x, Q |-/- False`



我们的构造过程推出了下面的结论

- `Gamma(n)` is consistent for all n;
- `P(n)` is an element of `Gamma(m)` if and only if `P(n)` is in `Gamma(n)` for any `n < m`;
- `Gamma(0)` is a subset of `Gamma(n)` for all n.


### Step 3.

构造`Gamma'`定义为所有`Gamma `的并集，我们证明`Gamma'`是极大一致集且有witness。

首先显然，`Gamma'`是一致的。

其次，由反证法，保证了`Gamma'`是极大一致的。

最后，case a保证了witness。


## Canonical Model Construction and Truth Lemma

> 我们主要关注一阶逻辑的符号层面的证明，不关心论域、函数、关系符号的解释（只要有一种满足即可）
> 对比程序逻辑推导的霍尔逻辑，+、-、*等函数符号应该是有论域解释的。

如何构造解释（构造对应的论域、~~函数~~、关系符号、自由变元），使得有witness的最大一致集在该解释之上可满足。

### Constructing the domain
First, we claim that the pairs of variables `x, y` such that `x == y` is a proposition in Gamma forms an equivalent relation.
1. `x==x`，一定在Gamma中（极大一致集），不然加进去之后推出矛盾
2. `x==y`推出`y==x`，利用极大一致性。
3. 传递性类似的，利用极大一致性。（即Gamma内能推出的命题一定在Gamma内）
Then, we define the domain D to be the equivalent classes of this relation. 构造的论域就定义为所有自由变元的一个等价类。即论域中的每个元素都是原来逻辑中自由变元的一个子集（论域是一个集合的集合）。

### Constructing the relation symbol's interpretation
We define the relation symbol `PRel`'s interpretation `Rel` as follows. Suppose `x*` and `y*` are two equivalent classes in the domain `D`取出等价类的代表元. The pair `x*`, `y*` is an element of Rel if and only if `PRel x y` is a proposition in Gamma. Here `x` and `y` represent elements of `x*` and `y*`.

注意：任选出来结果还是一样的，因为It is critical that Rel is well defined. In fact, if `x1 == x2`, `y1 == y2` and `PRel x1 y1` are elements of Gamma, `PRel x2 y2` must be its element too.

### Constructing variables' interpretation
每个变元对应哪一个论域中的对象？直接对应等价类。We simply let La be the function that La(x) = x*. Here, x* represents the equivalent class in D such that x is in it.

### Truth lemma

原结论，在Gamma中的都为真，我们证明一个更强的结论，且不在Gamma中的都不为真。（iff）

We prove by induction over P's syntax tree that P is an element of Gamma if and only if J = (D, Rel, La) satisfies P.

做结构归纳。

1. Case 1: `P` is `x1 == x2`.
   `P` is an element of Gamma if and only if `x1` and `x2` are in the same equivalent class in `D`, which is equivalent to say that `x1` and `x2` has the same denotation in `J`.
2. Case 2: `P` is `PRel x1 x2`.
   It is obvious by `Rel`'s definition. 与之前的定义类似
3. Case 3: `P` is PFalse.
   On one hand, `PFalse` cannot be `Gamma`'s element since it is consistent. On the other hand, `PFalse` is not satisfied by any interpretation, including `J`.
4. Case 4. `P` is `P1 IMPLY P2`.
   语义方面，由语义定义，要么 `J` does not satisfy `P1` or `J` satisfies `P2`, 也即 `P1` is not an element of `Gamma` or `P2` is an element of `Gamma`. 
   1. 若`P1`不在`Gamma`中，那么`Gamma`能推出`NOT P1`，但是`NOT P1`可以推出`P1 IMPLY P2`，在`Gamma`中了, 得证。
   2. 类似的若`P2`在`Gamma`中，那么`Gamma`能推出`P1 IMPLY P2`，在`Gamma`中了, 得证。
   反过来，语法层面，如果`P1 IMPLY P2`在`Gamma`中，是不是两种解释有一个成立？反证法：If `P1` is an element of `Gamma` and `P2` is not an element of `Gamma`, then `NOT P2` must be an element of `Gamma`. Thus, `NOT (P1 IMPLY P2)` is also an element of `Gamma` which means `P1 IMPLY P2` is not in `Gamma`.
   This tells us that `P1 IMPLY P2` is in `Gamma` if and only if `P1` is not in `Gamma` or `P2` is in `Gamma`.
5. Case 5. `P` is `FORALL x. P1`.
   On one hand, suppose `FORALL x. P1` is an element `Gamma`. We know that for any variable `y`, `P1 [x ⟼ y]` will also be `Gamma`'s element. By induction hypothesis, `J` satisfies `P1 [x ⟼ y]` （Recall 语法替换与语义替换等价）. Thus, no matter what value in D is reassigned to the interpretation of x, the new interpration will satisfy `P1`. So, `J` satisfies `FORALL x. P1`.
   On the other hand, suppose `FORALL x. P1` is not an element Gamma. 反证法 Then, `EXISTS x, NOT P1` will be an element of Gamma. According to the fact that Gamma is **witnessed**, there must exist a variable y such that `NOT P1 [x ⟼ y]` is in Gamma. Thus `P1 [x ⟼ y]` is not an element of `Gamma`. By induction hypothesis, `J` does not satisfy `P1 [x ⟼ y]` . So,
       ( D, Rel, La [x ⟼ y*] ) |=/= P1
   存在某一种解释中的替换，使得新的解释在`P1`不为真，那就是原来的解释上面，`FORALL x. P1`不为真，反证成功。which tells us that `J` does not satisfy `FORALL x. P1`.


到此为止，我们证明了典范模型的性质：
> Given `Gamma` which is witnessed and maximally consistent, we can construct an interpretation `J` satisfying all propositions in `Gamma`.

## Summary
FOL's completeness (weak completeness) can be established by the follwoing steps.
- Reducing weak completeness to **strong completeness**. Here, strong completeness means: if P is a consequence of Gamma, then P is derivable from Gamma. 语义后承推出强完全性。
- Reducing "consequence => derivable" to "consistent => satisfiable". This reduction step is done via proof by contradiction. 引入一致、可满足定义。只需证明一致集均可满足
- Proving that every consistent set can be expanded to a witnessed maximally consistent set. This construction is called Lindenbaum construction. 两步走，每一个一致集都可以扩张成为有见证者的极大一致集。
- Proving that every witnessed maximally consistent set is satisfiable. This conclusion is called truth lemma. It is proved by induction over propositions' syntax trees. 每一个有见证者的极大一致集均可满足。
It is worth noticing that this completeness theorem only says FOL is strong enough to prove properties of logic connectives. In other words, function symbols and relational symbols can be arbitrarily explained. Thus, we cannot say that our logic is strong enough to establish all properties about arithmetics. In fact, no logic is strong enough to achieve that —- this is Godel's incompleteness theorem.