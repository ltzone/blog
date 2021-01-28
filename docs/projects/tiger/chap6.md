---
title: Chapter 6 Activation Records
date: 2021-01-28 11:27:11
tags: 
- OCaml Compiler

categories: 
- Study


sidebar: True
lang: en-US
---


<!--more-->


::: warning Discussion: Is it necessary to keep local variables after a function has returned?

- No, in many languages (C, Pascal, Tiger, ...):
  - Pascal/Tiger have nested functions, but they do not have functions as returnable values
  - C has function as returnable values, but not nested functions
  - can use stack to hold local variables
- Yes, in ML, Scheme, and several other languages:
  - nested functions, where inner functions may use variables defined in outer functions
  - functions returned as results cause local variables to need longer lifetimes than function invocations
  - combination = higher-order functions
  - An example:

```SML
fun f(x) = 
    let fun g(y) = x+y (* nested function *)
    in g (* function as results *)
    end

val h = f(3) (* 3 can't be destroyed after return *)
val j = f(4)

val z = h(5) (* invoke f(3) *)
val w = j(7)
```
:::

In this chapter, we focus on stackable local variables.

### 1 Stack Frames

1. Why stack **frames**?
   - Local variables are pushed and popped in batches
   - Sometimes we want to access variables deep in stack
2. The area on the stack devoted local variables/parameters/return address for a function is called the function's **activation record** or **stack frame**
3. For historical reasons, runtime stacks usually start at a high memory address and grow downward

