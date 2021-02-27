---
title: Homework1 - Y86 & HCL
date: 2021-02-27 21:53:44
tags: 
- CSAPP

categories: 
- Study

sidebar: true
lang: en-US
---

Solution to [Homework 1](https://ipads.se.sjtu.edu.cn/courses/ics/hws/hw-2-1.pdf), HCL & Y86 Instruction Exercise


<!-- more -->

## Exercise 1

1. `bool NAND = !a || !b`
2. `XOR3` is implemented as follows 
   ```
   word XOR3 = [
       a == b && b == c : 1;
                      1 : 0;
   ]
   ```


## Exercise 2

1. blanks
   1. `30f50002000000000000`
   2. `irmovq   $3, %rsi`
   3. `xorq     %rax, %rax`
   4. `mrmovq   (%rdx), %rcx`
   5. `6260`
   6. `.pos 0x200`
   7. `0x320`
2. `%rax` is `1`