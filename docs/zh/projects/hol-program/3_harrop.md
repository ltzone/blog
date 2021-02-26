---
title: 3 First-Order Hereditary Harrop Formulas 导读
date: 2021-02-22 19:27:13
tags: 
- Lambda Prolog

categories: 
- Courses

sidebar: true
lang: zh-CN
---

霍恩子句形式的逻辑程序要求证明目标中不含全称量词和蕴含关系符。本章我们会介绍另一类式子， Hereditary Harrop Formulas 。在 Hereditary Harrop Formulas 中，由于引入了全称量词和蕴含关系符，在计算搜索证明的过程中程序和签名都会动态变化。


<!-- more -->

## 1 The syntax of goals and program clauses

本节介绍了 Hereditary Harrop Formulas 的格式，如下所示。

![](./img/02-22-20-22-54.png)

注意到，证明目标现在允许全称量词和蕴含操作符，而逻辑程序中则不允许顶层出现析取或存在量词。

Hereditary Harrop Formulas 也可以通过计算子式的“正负性”进行定义。G-公式的正子式还是G-公式，负子式是D-公式，类似地，D-公式的正子式还是D-公式，负子式是G-公式。此外，一阶霍恩子式不存在负子式。

定义了 clausal order，将会在第七章用到。

本节提出的语法和第二章中的 AUGMENT/GENERIC 规则是兼容的，因此O-proof 依然可以基于 fohc 的规则进行计算。


## 2 Implication Goals

注意到在 fohc 中，程序和签名在计算的过程中保持不变，本节我们可以发现，对蕴含操作符，搜索的过程中，程序签名中的命题会像栈一样先进后出地动态变化。

在实现中，我们一般使用深度优先的搜索策略，这可能会导致程序不停或者耗时长的问题。

2.3 给出了基于命题的推理实现数据库 query 的例子。

## 3 Universally Quantified Goals

与引入命题类似，逻辑变量也可以使用类似的方法在证明搜索的过程中被引入。

基于逻辑变量，我们可以借助一些中间变元，完成更复杂命题的推理。

引入逻辑变元后，我们需要对程序中变量的作用域进行管理。否则声明的语义可能会与期望不一致。

3.1 说明了变元替换必须作用于非自由出现的变元
3.2 用`reverse`的例子说明了 fohh 的命题可以支持将子句和证明目标中的逻辑变量连接起来。


## 4 The relationship to logical notions

- 经典逻辑不能为 $\lambda$Prolog 提供声明式的语义
- 直觉主义逻辑规定 `false` 可以推出一切，而极小逻辑仅规定 fa`lse 是一个非逻辑常量
-  $\lambda$Prolog 的操作语义在极小逻辑中是完全的
- 在 $\lambda$Prolog 的操作语义中，我们可以通过先检查当前程序是否可以推出 `false`，达到直觉主义逻辑的要求。所以  $\lambda$Prolog 在直觉主义逻辑中也是完全的。

4.3 介绍了一些 fohh 的子集。