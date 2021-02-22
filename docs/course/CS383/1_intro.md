---
title: Introduction
date: 2021-02-22 12:57:00
tags: 
- Programming Languages

categories: 
- Courses

sidebar: true
lang: en-US
---

<!-- more -->


Not about programming, not about compiler, We will focus more on the design of the language (the interpretation/semantics). We care less about the performance or implementation of the language.

- **Theoretical aspects** of the **design** and **implementation** of **all** programming languages
- The **commonalities** and **differences** between various paradigms and languages

So you can
- Pick the right language
- Design your own language
- Do PL research


## Principles

The Factorial Program
- In C, the factorial is implemented as a function
- In Java, the factorial is implemented as a class
- In Scheme, ... as a recursion function *(closet to original math definition)*
  ```scheme
  (define (factorial n) (if (< n 1) 1 (* n (factorial (- n 1)))))
  ```
- In prolog, ... as recursion (using decoration)

Above all, four programming paradigms. The way we **model** the problem may differ

Programming Languages have four properties
- Syntax
- Names
- Types
- Semantics

For any language:
- Its designers must define these properties
- Its users must master these properties

### Syntax

::: tip Syntax

a precise description of all its grammatically correct programs
- vocabulary: all tokens/words
  - C++ divide tokens into keywords, literals, constants and punctuations
- grammar
- how error detected and caught

:::

### Name (Identifier)

An entity is **bound** to a name (identifier) within the context of:
- Scope (static/dynamic)
- Visibility (part of scope that is visible) `tenv/venv`
- Lifetime (dynamic and runtime)
- Type

### Types

A *type* is a collection of values and collection of legal operations on those values.

- simple types
- structured types
- function types $\rightarrow$
- **generic types (polymorphism)** $\alpha$

### Semantics

- operational semantics
  - `fact = fact * c` tells the value of `fact` changes stm after stm
- static semantics
  - What does `if` mean? Can be told only by looking at the program
- dynamic semantics


## Paradigms

different paradigms have different problem-solving perspectives

- Imperative
- Object-oriented
- Functional
- Logic / Declearative

### Imperative

Classical von Neumann-Eckert model:
- Program and data are indistinguishable in memory
- Program = a sequence of commands
- State = values of all variables when program runs
- Large programs use procedural abstraction



### Object-oriented
An OO Program is a collection of objects that interact by **passing messages** that transform the state

When studying OO, we learn about
- Sending Messages
- Inheritance
- Polymorphism

### Functional

models a computation as a collection of mathematical functions.
- Set of all inputs = domain of function
- Set of all outputs = range of function

Characterized by
- Functional Composition
- Recursion
- No state changes: `x := x + 1` is wrong

### Logic

We specify **what** outcome is expected instead of **how** it should be accomplished (**Declarative**)

We study
- Programs as sets of constraints on a problem
- Programs that achieve all possible solutions
- Programs that are nondeterministic

Example languages: Prolog, CLP


### Modern Languages are Multi-Paradigm

- Haskell = F + I
- Scala = F + I + O
- OCaml = F + I + O
- F# = F + I + O
- Python = O + I + F


## Special Topics

- Concurrency
- Event Handling
- Correctness


## A Brief History

Different PLs are invented by different communities
- AI - Prolog, CLP, (Python)
- CS Education - Pascal, Logo
- Science and Engineering - Fortran, Ada, ML, Haskell
- Information Systems - Cobol, SQL
- System and Networks - C, C++, Perl, Python
- WWW - HTML, Java, JavaScript, PHP


## On Language Design

What is the design principle of PL design?
- Computer Architecture
- Technical Setting
- Standards
- Legacy Systems (both HW and SW systems)

### What makes a successful language

1. Simplicity and Readability
   - Small Instruction Set
    - e.g. ~~Java~~ and Scheme
   - Simple syntax
    - e.g. ~~C/C++/Java~~ and Python
   - Benefits
    - Ease of learning
    - Ease of programming
2. Clarity about binding
   - variable name to its value/type
   - **early binding** takes place at compile time (a lot of functional, many new languages)
   - **late binding** takes place at run time (a lot of imperative)
3. A language is **reliable** if
   - Program behavior is same on different platforms
   - Type errors are detected
     - ~~C~~ vs Haskell
   - Semantic Errors are properly trapped
     - ~~C~~ vs C++
   - Memory leaks are prevented
     - ~~C~~ vs Java
4. Language Support
   - Accessible (public domain) compilers/interpreters
     - Java (opened) vs. C# (closed)
   - Good texts and tutorials
   - Wide community of users
   - Integrated with development environments
5. Abstraction in Programming
   - **Data Abstraction**
     - some prefer Programmer-defined types/classes
     - while others provide users with a wide range of Class libraries
   - **Procedural Abstraction**
     - Programmer-defined functions
     - Standard function libraries
6. Orthogonality (minimumism)
   - All features should be built upon a **small, mutually independent** set of primitive operations
     - `while` vs `for` loop in C are quite related, not an orthogonal design
     - in pure Scheme, the only way to write a loop is to use recursion
   - Fewer exceptional rules = conceptual simplicity
     - e.g. restricting types of arguments to a function
   - Tradeoffs with efficiency
     - which is why sometimes orthogonality is disobeyed
     - sometimes users may enjoy such redundancy in your designed language for productivity
7. Efficient Implementation
   
   "Efficient" is defined by our tasks
   - Embedded Systems
     - Real time responsiveness
     - Resources
   - Web Applications
     - Responsiveness to users
   - Corporate Database Applications
     - Searching and Updating
   - AI Applications
     - Modeling Human Behaviors

8. Compiler and Interpreters
   - Compiler - produces machine code
   - Interpreter - executes instructions on a virtual machine

