---
title: Chapter 6 Activation Records
date: 2021-02-03 11:27:11
tags: 
- OCaml Compiler

categories: 
- Study


sidebar: True
lang: en-US
---


<!--more-->

## Introduction

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

## 1 Stack Frames

1. Why stack **frames**?
   - Local variables are pushed and popped in batches
   - Sometimes we want to access variables deep in stack
2. The area on the stack devoted local variables/parameters/return address for a function is called the function's **activation record** or **stack frame**
3. For historical reasons, runtime stacks usually start at a high memory address and grow downward

### The structure of a Stack


| <- Higher Address  |                    |                    |                   | ...              |
|--------------------|--------------------|--------------------|-------------------|------------------|
|                    | ... Previous Frame | Current Frame...   |                   | ...              |
| Argument n, ..., 1 | Static Link        | Local Variables    | Return Address    | ...              |
|                    | ↑ Frame Pointer    |                    |                   | ...              |


| ...                |                    |                    |                   | Lower Address -> |
|--------------------|--------------------|--------------------|-------------------|------------------|
| ...                |                    |                    | ... Current Frame | Next Frame ...   |
| ...                | Saved Registers    | Outgoing Arguments | Static Link       | Garbage          |
| ...                |                    |                    | ↑ Stack Pointer   |                  |


### Stack Issues in Compilation

1. **The frame pointer**, Why talk about it? Why not constant? Because *the frame size is not known until quite late in the compilation process*, so for convenience, we still talk about frame pointer, and assume formals and locals **near** frame pointer while temporaries and saved registers **far** away, at offsets that are known later.

2. **Registers**, on most architectures, caller-save/callee-save is not built into hardware, but a convention described in the machine's reference manual. This chapter will not touch such issues. We will leave the duty to register allocator to ensure a wise selection of register for each local variable and temporary.

3. **Parameter Passing**, traditional conventions let function arguments be passed on stack, but this causes needless memory traffic. The use of registers save time in one (or multiple) ways as follows:
   1. **leaf procedures** don't need to write incoming arguments into memory, (often don't need a stack frame at all)
   2. **interprocedural register allocation** used by some optimizing compilers
   3. **dead variables** can be overwritten to pass parameters
   4. Some architectures have **register windows**

   Issue - **dangling reference**: the fact that C programming language allows taking the address of a formal parameter and using it as consecutive address causes a contradiction that parameters are *passed in registers, but have addresses too*. One solution is to let the calling function reserve space for the register arguments and let the called function write to it if necessary. Another solution is to use call-by-reference to avoid this issue.

4. **Return Address**, on modern machines, the `call` instruction will put the return address to a designated register, and for a non-leaf procedures, (unless interprocedural register allocation is used) it will also write the return address to the stack.

5. **Frame Resident Variables**, a variable **escapes** if it is passed by reference, its address is taken or it is accessed from a nested function, during which case it should be written onto the stack. Unfortunately, these conditions don't manifest themselves early as much, so we need to traverse the whole program to find out whether a local variable escapes or not.

6. **Static links**, Tiger allows nested function declarations,the inner functions may use variables declared in outer functions. Such language feature is called **block structure**. To make this work, serveral methods are available
   1. **Static Link** pass an extra pointer to the frame of the funtion statically enclosing the called procedure, forming a chain of stack links. This will be adopted in our compiler
   2. Global array mapping nesting depth to the frame of the most recently entered procedure of this depth (**display**)
   3. **lambda lifting**

## 2 Frames in Tiger Compiler & Implementation

In the programming project of this chapter, we introduce some abstract layers to our compiler representing some basic notions of stack frame. The structure of our current program is displayed as follows.

![](./img/02-03-22-46-15.png)

The duties of different modules
- `Semant`: Traverse the Abstract Syntax Tree, Type checking, call `Translate` where necessary
- `Translate`: interfaces the machine-dependent frame layout from the source-language's point of view
- `Frame` interfaces the machine-dependent frame layout from the target machine's point of view. It defines a module type signature, and different target languages can have different implementations of `Frame` module
- `Temp`, since it's too early to determine exactly which registers are available or where the procedure body will be located, we use this module to abstract these two differnet types of data access.

The textbook has provided a detailed introduction to the organization and signature of the above modules, related issues involve
- Representations of frame descriptions
- Local variables: signature declaration of `Frame` module
- Calculating Escapes: how to calculate escape before everything in `Semant` begins
- Temporaries and Labels: details of `Temp` module
- Two layers of abstraction: organization of the abstract layers
- Managing static links: implement static links in `Translate`
- Keeping track of levels: how to augment `Semant` to pass the current level value

Some of the important comments have been quoted as comments of my implementation. For details, you may check `tiger/lib/analysis` for details.

## Exercises

TBD

## References

[MIPS Calling Convention](https://courses.cs.washington.edu/courses/cse410/09sp/examples/MIPSCallingConventionsSummary.pdf)