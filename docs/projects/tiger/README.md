---
title: Modern Compiler Implementation in OCaml
date: 2021-01-26 11:00:35
tags: 
- OCaml Compiler

categories: 
- Study

sidebar: True
lang: en-US
---

In this piece of work, I will try to implement a compiler of the tiger language through OCaml under the guidance of "Modern Compiler Implementation in ML".

<!--more-->

Solution to "Modern Compiler Implementation in ML" implemented in Ocaml

![RoadMap](https://www.cs.princeton.edu/~appel/modern/text/prefdag.gif)

## Environment

- WSL:Ubuntu 18.04
- dune 2.6.2
- OCaml 4.10.0

## My Progress

### Chapter 1 Introduction
- :heavy_check_mark: Reading (*January 2020*)
- :heavy_check_mark: Programming: [Straight-Line Interpreter](exercises/chap1/slp.ml) (*January 2020*)
- :black_square_button: Exercises 
  - :heavy_check_mark: [Basic BST](exercises/chap1/bst.ml) (*January 2020*)
  - :black_square_button: Balanced BST

### Chapter 2 Lexical Analysis
- :heavy_check_mark: Reading (*May 2020*)
  - :heavy_check_mark: [Foundation Notes](./chap2) (*July 2020*)
  - :black_square_button: Implementation Notes (will be revisited after parser)
- :black_square_button: Programming: use OCamllex to generate a lexer for Tiger Language
- :black_square_button: Exercises

### Chapter 3 Parsing
- :heavy_check_mark: Reading (*Aug 10th, 2020*)
  - :black_square_button: Foundation Notes
  - :heavy_check_mark: [Implementation Notes](./chap3#implementation) (*Aug 15th, 2020*)
- :heavy_check_mark: Programming: use Menhir to write the parsing rule for Tiger Language 
  - :heavy_check_mark: [Basic Rules](tiger/lib/frontend/parser.mly)  (*Aug 15th, 2020*)
  - :black_square_button: (Optional) Implement some error recovery strategies
- :black_square_button: Exercises

### Chapter 4 Abstract Syntax
- :heavy_check_mark: Reading (*Aug 14th, 2020*)
  - :heavy_check_mark: [Foundation Notes](./chap4) (*Aug 25th, 2020*)
  - :heavy_check_mark: [Implementation Notes](./chap4#implementation) (*Aug 20th, 2020*)
- :black_square_button: Programming: Add semantic actions to the parser
  - :heavy_check_mark: Transplant the `Symbol` [library](tiger/lib/ast/symbol.ml) (a module to turn string into symbols)  (*Aug 15th, 2020*)
  - :heavy_check_mark: Semantic Actions: [build AST](tiger/lib/frontend/parser.mly) (*Aug 20th, 2020*)
  - :heavy_check_mark: [Driver](tiger/driver/util.ml) and [Test Cases](tiger/testcases) (*Aug 20th, 2020*)
  - :heavy_check_mark: Explicitly resolve shift/reduce conflicts (*Aug 20th, 2020*)
  - :heavy_check_mark: a better `pos` setting (*Jan 28th, 2021*)
  - :black_square_button: More Error Recovery,
- :black_square_button: Exercises
  - :heavy_check_mark: 4.1 Regular Expression Abstract Syntax (*Aug 25th, 2020*)
  - :heavy_check_mark: 4.2 ~ 4.4 Straight Line Interpreter implemented in Menhir through semantic actions (*Aug 25th, 2020*)
  - :black_square_button: 4.5 Straight Line Interpreter implemented in Recursive Descent
  - :black_square_button: 4.6 rewrite recursion direction

> To Run the parser, `cd tiger; make utop`, then execute `Util.Semant_Util.parse_file "testcases/yourtestfile.tig"` in utop to check the parsed syntax tree

### Chapter 5 Semantic Actions
- :heavy_check_mark: Reading
  - :heavy_check_mark: [Foundation Notes](./chap5) (*Aug 27th, 2020*)
  - :heavy_check_mark: [Implementation Notes](./chap5) (*Oct 9th, 2020*)
- :heavy_check_mark: Programming Part A: (*Sept 2nd, 2020*)
  - :heavy_check_mark: [Simple Type Checker](tiger/lib/analysis/semant.ml) (*Aug 31st, 2020*)
  - :heavy_check_mark: [Declaration Processor](tiger/lib/analysis/semant.ml) (*Sept 2nd, 2020*)
- :black_square_button: Programming Part B:
  - :heavy_check_mark: [Handle (Mutually) Recursive Functions, Types Declarations](tiger/lib/analysis/semant.ml) (*Sept 2nd, 2020*)
  - :black_square_button: Correct Nesting of break statements
  - :heavy_check_mark: [Driver](tiger/driver/semant_util.ml) and [TestCases](tiger/testcases/semant_output.txt) (*Oct 9th, 2020*)
- :black_square_button: Exercises
  - :black_square_button: Improve HashTable Implementation
  - :black_square_button: efficient data structure for environment "adding"
  - :black_square_button: cycle of type definitions

> To Run the type checker, `cd tiger; make utop`, then execute `Util.Semant_Util.run_test()` in utop to type check all the tiger programs

## References

- Textbook: http://cs.princeton.edu/~appel/modern/ml/

- Ocaml Tutorial: https://ocaml.org/learn/tutorials/index.zh.html

- Real World OCaml: http://dev.realworldocaml.org/

- Ocaml Standard Library: http://caml.inria.fr/pub/docs/manual-ocaml/libref/index.html

- SML to Ocaml CheatSheet: https://people.mpi-sws.org/~rossberg/sml-vs-ocaml.html

