---
title: Lab 2 Bomb Lab
date: 2021-01-29 23:51:48
tags: 
- CSAPP

categories: 
- study

sidebar: True
lang: en-US
---


<!--more-->


## GDB Cheatnotes

- break points
  - `break main` pause before entering main
  - `clear main` removes breakpoint
- control excution
  - `run args` start execution
  - `continue` continue untils another breakpoint
  - `nexti` step through a single x86 instr, will display the next instr
- utils
  - `disassemble`, show the current assembly, the pointer points to the next instruction to be executed
  - `disassemble main` show the assembly instructions in main
  - `print [type] [var]`, where \[type\] can be `/x`(hex), or `(char*)`(string), and \[var\] can be `0x...`(memory) or `$rsi`(register)



## Assemble Cheatnotes
- `$rdi`, `$rsi`, `$rdx`, `$rcx` 1~4th argument

## Defusing Bombs

### Bomb 1

Make breakpoints at phase_1, `disassemble`:

Dump of assembler code for function phase_1:

```
=> 0x0000000000400ee0 <+0>:     sub    $0x8,%rsp
   0x0000000000400ee4 <+4>:     mov    $0x402400,%esi
   0x0000000000400ee9 <+9>:     callq  0x401338 <strings_not_equal>
   0x0000000000400eee <+14>:    test   %eax,%eax
   0x0000000000400ef0 <+16>:    je     0x400ef7 <phase_1+23>
   0x0000000000400ef2 <+18>:    callq  0x40143a <explode_bomb>
   0x0000000000400ef7 <+23>:    add    $0x8,%rsp
   0x0000000000400efb <+27>:    retq   
```

The key not to explode the bomb is to make the two string equal, so that `$eax` will then be 0, and `je` will be triggered, skipping the bomb.

The first argument in `string_not_equal` is the line we've input, and the second argument seems to be related to address `0x402400` in `$esi`. Through `(gdb) print (char*) 0x402400`, we can find that line.

That's the solution to the first bomb.

### Bomb 2

Dump of assembler code for function phase_2:
```
=> 0x0000000000400efc <+0>:     push   %rbp
   0x0000000000400efd <+1>:     push   %rbx
   0x0000000000400efe <+2>:     sub    $0x28,%rsp
   0x0000000000400f02 <+6>:     mov    %rsp,%rsi
   0x0000000000400f05 <+9>:     callq  0x40145c <read_six_numbers>
   0x0000000000400f0a <+14>:    cmpl   $0x1,(%rsp)
   0x0000000000400f0e <+18>:    je     0x400f30 <phase_2+52>
   ...
```

Phase 2 calls `read_six_numbers` function

```
Dump of assembler code for function read_six_numbers:
   0x000000000040145c <+0>:     sub    $0x18,%rsp
   0x0000000000401460 <+4>:     mov    %rsi,%rdx
   0x0000000000401463 <+7>:     lea    0x4(%rsi),%rcx
   0x0000000000401467 <+11>:    lea    0x14(%rsi),%rax
   0x000000000040146b <+15>:    mov    %rax,0x8(%rsp)
   0x0000000000401470 <+20>:    lea    0x10(%rsi),%rax
   0x0000000000401474 <+24>:    mov    %rax,(%rsp)
   0x0000000000401478 <+28>:    lea    0xc(%rsi),%r9
   0x000000000040147c <+32>:    lea    0x8(%rsi),%r8
   0x0000000000401480 <+36>:    mov    $0x4025c3,%esi
   0x0000000000401485 <+41>:    mov    $0x0,%eax
   0x000000000040148a <+46>:    callq  0x400bf0 <__isoc99_sscanf@plt>
   0x000000000040148f <+51>:    cmp    $0x5,%eax
   0x0000000000401492 <+54>:    jg     0x401499 <read_six_numbers+61>
   0x0000000000401494 <+56>:    callq  0x40143a <explode_bomb>
   0x0000000000401499 <+61>:    add    $0x18,%rsp
=> 0x000000000040149d <+65>:    retq  
```

Note that `read_six_numbers` may also trigger a bomb, and it calls a `sscanf` function. By printing out the formatter string, `print (char*) 0x4025c3`, we can know that the input should be in the format of `%d %d %d %d %d %d`. And inadequate number of args will trigger the bomb.

There goes the rest of the code. The numbers read by `read_six_numbers` are accessed by `phase_2` from the stack frame. So `(%rbx)` will refer to the first number, and `0x4(%rbx)` refers to the second number. The remaining of the codes are actually a loop on the six numbers. 

`<+14>:    cmpl   $0x1,(%rsp)` indicates that the first number should be 1, which can be checked by `(gdb) x /d $rsp`. Then every next number will be the double of the previous number, indicated by `mov    -0x4(%rbx),%eax; add    %eax,%eax; cmp    %eax,(%rbx)`. 


```
   ...
   0x0000000000400f10 <+20>:    callq  0x40143a <explode_bomb>
   0x0000000000400f15 <+25>:    jmp    0x400f30 <phase_2+52>
   0x0000000000400f17 <+27>:    mov    -0x4(%rbx),%eax
   0x0000000000400f1a <+30>:    add    %eax,%eax
   0x0000000000400f1c <+32>:    cmp    %eax,(%rbx)
   0x0000000000400f1e <+34>:    je     0x400f25 <phase_2+41>
   0x0000000000400f20 <+36>:    callq  0x40143a <explode_bomb>
   0x0000000000400f25 <+41>:    add    $0x4,%rbx
   0x0000000000400f29 <+45>:    cmp    %rbp,%rbx
   0x0000000000400f2c <+48>:    jne    0x400f17 <phase_2+27>
   0x0000000000400f2e <+50>:    jmp    0x400f3c <phase_2+64>
   0x0000000000400f30 <+52>:    lea    0x4(%rsp),%rbx
   0x0000000000400f35 <+57>:    lea    0x18(%rsp),%rbp
   0x0000000000400f3a <+62>:    jmp    0x400f17 <phase_2+27>
   0x0000000000400f3c <+64>:    add    $0x28,%rsp
   0x0000000000400f40 <+68>:    pop    %rbx
   0x0000000000400f41 <+69>:    pop    %rbp
   0x0000000000400f42 <+70>:    retq   
End of assembler dump.
