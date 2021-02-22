---
title: 2 First-Order Horn Clauses
date: 2021-02-17 10:20:54
tags: 
- Lambda Prolog

categories: 
- Study

sidebar: true
lang: en-US
---


In this chapter, we want to develop a view of logic programming that will allow us to introduce extensions smoothly in later chapters, leading eventually to the full set of logical features that underlie the $\lambda$Prolog language. In particular,

1. **a relational approach to programming**, relations over data descriptions are defined or axiomatized through formulas that use logical connectives and quantifiers.
2. **computation should be viewed as a search process**, which should be realized by according to each logical symbol a fixed search-related interpretation.

We will present **first-order Horn clauses** as a specific elaboration of this framework


<!-- more -->


## 1 First-order Formulas

- Now, we permit the target types of constants to be `o`, constants that have this type are called *relation* or *predicate* symbols.
- **Well-formed** *(according to same typing rule in Section 3, Chapter 1)* expressions that have the **type `o`** are referred to as **first-order atomic formulas.** For instance, 
  - `type  memb       A -> list A -> o.` and `type  append     list A -> list A -> list A -> o.` are first-order predicate symbols
  - `memb 1 (1 :: 2 :: nil)` is an atomic formula

::: tip
In $\lambda$Prolog, to permit the construction of complex formulas, we add to signatures a special, pre-defined set of *logical constants or propositional symbols.*

- `true` of type `o` representing $\top$,
- `=>` of type `o -> o -> o` representing $\implies$, infix, right associative
- `&` of type `o -> o -> o` representing $\cap$, infix, right associative
- `,` of type `o -> o -> o` representing $\cap$, infix, left associative
- `;` of type `o -> o -> o` representing $\cup$, infix, left associative
- `:-` of type `o -> o -> o` representing implication written in reverse, infix, non associative

Note, with `o` as argument type, these quantifiers are a violation of the restriction placed earlier. We permit this violation in the first-order setting only with respect to the types of these logical constants

:::

The final addition that leads to the full set of first-order formulas is that of universal and existential quantification. Both forms of quantification range over explicit domains specified by types, written as $\forall_{\tau} F$ and $\exists_{\tau} F$ respectively. Both quantifiers **bind** a variable and establish a **scope** for its binding.

::: tip

In $\lambda$Prolog, we write `(pi (x:T)\ F)` and `(sigma (x:T)\ F)` respectively, where `F`, `T`, `x` are conrete syntax renditions of the formula $F$, type $\tau$ and the variable $x$.

Note, the type can often be left implicit, to be filled in in a most general way that we describe shortly. i.e. given in `(pi x\ F)` and `(sigma x\ F)`

`\` plays the role of a binding operator, which will become precise in Chapter 4 as an infix operator.

By convention, the scope of a bound variable introduced by a backslash `\` extends as far to the right as is possible, limited only by parentheses and the end of the expression.

:::


A few examples with quantifiers
```
pi x\ pi k\ memb x (x :: k)
pi X\ pi L\ pi K\ pi M\ append (X::L) K (X::M) :- append L K M
sigma X\ pi y\ sigma h\ append X y h
```

::: tip
the syntax of bound variable names can be any contiguous sequence of characters beginning with an upper or lower case letter.
:::

An important principle concerning quantification is that the pattern of binding is key and **the names chosen** for variables to indicate this structure are **unimportant**. (resulting from $\alpha$-renaming, detail in Chapter 5)

## 2 Logic Programming and Search Semantics

TBD...
