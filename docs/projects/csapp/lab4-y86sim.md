---
title: Lab 4 Y-86 Simulator
date: 2021-03-16 21:03:18
tags: 
- CSAPP

categories: 
- Study

sidebar: true
lang: en-US
---


<!-- more -->


## Materials

- Course Homepage - [SJTU-IPADS-ICS2021](https://ipads.se.sjtu.edu.cn/courses/ics/schedule.shtml)
- Lab [Handout](https://ipads.se.sjtu.edu.cn/courses/ics/labs/lab4.pdf)
- [Codes](https://github.com/ltzone/csapp-lab/blob/master/lab4/y64sim.c)

## Tips

1. Make use of the util functions such as `set_xxx_val`, `get_xxx_val`
2. Make use of the interface, e.g. `./yat -c` for correct answer
3. Use GDB to make a breakpoint at `nexti` entry helps with efficient debugging
4. Remember to add some `err_print` into the skeleton, in order to pass the test and get the score.