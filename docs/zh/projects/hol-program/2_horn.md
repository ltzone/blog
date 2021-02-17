---
title: 2 First-Order Horn Clauses 导读
date: 2021-02-17 22:17:53
tags: 
- Lambda Prolog

categories: 
- Study

sidebar: true
lang: zh-CN
---

本章介绍了$\lambda$Prolog作为编程语言需要的一些特性。在$\lambda$Prolog中，“程序”是通过“关系”描述的，“计算”的概念则是通过证明的“搜索”过程进行实现的。为此需要对上一章中描述的一阶逻辑进行扩展。**First-order Horn clauses**是我们在本章对这一框架扩展的具体实现。


<!-- more -->


## 1 First-order Formulas

- 定义了原子公式(atomic formulas)的概念和构成
- 介绍了$\lambda$Prolog中预定义的一系列逻辑常量/命题符号（logical constants or propositional symbols）
- 介绍了$\lambda$Prolog中存在谓词、任意谓词的实现，及其对应的类型规则
- 绑定变量的名称不会影响公式的等价性，将在第四章作介绍
- 反斜杠作为引入新绑定的语法，将在第四章作介绍。
- 可以使用第一章第五节中的unification算法完成绑定变量类型的推导

## 2 Logic Programming and Search Semantics

对于非原子命题，我们分析了AND/OR/INSTAN/AUGMENT/GENERIC/TRUE情况下对应的搜索行为。这些行为与签名和具体的程序无关，只和我们引入的逻辑常量有关。因此我们可以提出了一系列Right-introduction rules，将逻辑常量放到判断式$\Sigma ; \mathcal{P} \longrightarrow G$右边。在第五章第二节引入高阶项后，我们会介绍更加泛化的规则。

不难得出， Right-introduction rules 是有效的。但不是完备的。两个主要问题：首先，“析取”意味着公式中存在不确定性。此外，经典逻辑的框架中如排中律等假设也引入了这样的不确定性，因此我们将采用更弱的直觉主义逻辑。

与右引入规则对应的是左引入规则，左引入规则的主要作用是用来规约原子证明目标，这些不会被放入当前的框架中。

我们规定，一个判断式的解是所有应用INSTAN规则时引入的替换的集合。在一阶逻辑的Horn Clauses场景下，AUGMENT/GENERIC规则是多余的，但我们将在第三章基于这两条规则扩展一个更具表达力的编程语言。


## 3 Horn Clauses and their Computational Interpretation

我们通过排除一些逻辑常量的使用，规定了一类特殊形式的公式，称为 Horn Clauses （霍恩子句）。如果一个判断式中，所有在逻辑程序中的式子都是霍恩子句形式的，那么我们可以选择一条应用到证明目标上，从而在不改变逻辑程序的情况下，通过改变证明目标完成证明搜索的计算。该过程称为 backchaining （反链接）。

通过为霍恩子句每一个构造方式设计对应的反链接规则，我们就可以实现一系列证明过程的搜索。对一阶霍恩子句而言，可以证明这些规约是既有效且完备的。且在证明推进过程中，签名和逻辑程序可以保持不变。

后续章节中，我们同样会基于 AUGMENT/GENERIC 规则对现有语言进行拓展。

## 4 Programming with first-order Horn Clauses

- 4.1节介绍了上述概念在 $\lambda$Prolog 中的格式，以及一些语法糖层面的事项
- 4.2节介绍了 $\lambda$Prolog 系统的交互方式，和使用的一些细节，可以参考该系列 [Teyjus Tutorial](https://www.youtube.com/watch?v=q4uMTH91c-g) 视频作进一步参考
- 4.3节以有限状态机为例介绍了一个 $\lambda$Prolog 实例
- 4.4节以平衡二叉树为例介绍了另一个 $\lambda$Prolog 实例
- 4.5在 $\lambda$Prolog 中实现了一个用抽象语法表示的推理系统
 
注意，有关内置操作符、求值顺序等一些问题将在第六章作进一步讨论。

## 5 Pragmatic Aspects of Computing with Horn Clauses

TBD...