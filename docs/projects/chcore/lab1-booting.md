---
title: Lab 1 - Booting a Machine
date: 2021-01-29 16:36:59
tags: 
- Modern Operating Systems

categories: 
- Study

sidebar: True
lang: en-US
---


<!--more-->

## Exercise 1: ARM Instructions

1. Armv8 is the next major architectural update after Armv7. It introduces a 64-bit architecture, but maintains compatibility with existing 32-bit architectures. It uses two execution states: **AArch32** (**A32/T32** Instruction Sets) & **AArch64** (**A64** Instruction sets)
2. `mov dst, src`


## Exercise 2: Bootloader and Entry

- `make gdb`
- `(gdb) where`


## Exercise 3: Entry of kernel

- `(gdb) break main` the main function is defined in `kernel/main.c`
- `(gdb) continue`

For other cores, they will hang themselves up. The instruction is found in `boot/start.S`
```
  /* hang all secondary processors before we intorduce multi-processors */
secondary_hang:
	bl secondary_hang
```

## Exercise 4: LMA & VMA

VMA and LMA are the same in every segment.

## Exercise 5: Kernel Function: printk

Solution: make use of the buffer and let it grow in a backward direction. `s` will be passed to the `prints()` function, indicating the real beginning of the string to be printed.

```C
// kernel/common/printk.c:100:printk_write_num()
//
// store the digitals in the buffer `print_buf`:
// 1. the last postion of this buffer must be '\0'
// 2. the format is only decided by `base` and `letbase` here
int buf_idx = PRINT_BUF_LEN - 1;
print_buf[buf_idx] = '\0';
while (buf_idx >= 0 && u != 0){
    int rem = u % base;
    if (rem < 10){
        print_buf[--buf_idx] = '0' + rem;
    } else {
        print_buf[--buf_idx] = letbase + rem - 10;
    }
    u = u / base;
    width--;
}
s = print_buf + buf_idx;
```

## Exercise 6: Initialize SP and FP

- `$sp,$fp` are initialized at the beginning of function `start_kernel`

![](./img/02-02-16-15-23.png)


## Exercise 7, 8: Stack Structure and Parameter Passing

In a stack frame, from higher address (pointed by current frame pointer `%x29`) to lower address: stored-fp, arguments, return address(LR).

![](./img/02-02-15-54-01.png)

## Exercise 9: Implement stack_backtrace


```C
// In kernel/monitor.c
static inline __attribute__ ((always_inline))
u64 get_mem_val(u64 fp, u64 ofs)
{
	u64 goal;
	__asm __volatile("ldr %[goal], [%[fp], %[ofs]]"
						:[goal]"=r"(goal)               /* output */
						:[fp] "r"(fp), [ofs] "r" (ofs)  /* input */);
	return goal;
}

__attribute__ ((optimize("O1")))
int stack_backtrace()
{
	printk("Stack backtrace:\n");

	u64 cur_fp = read_fp();
	cur_fp = get_mem_val(cur_fp, 0x0);
	u64 lr, arg1, arg2, arg3, arg4, arg5;
	do {
		lr = get_mem_val(cur_fp, 0x8);
		arg1 = get_mem_val(cur_fp, -0x10);
		arg2 = get_mem_val(cur_fp, -0x8);
		arg3 = get_mem_val(cur_fp, 0x0);
		arg4 = get_mem_val(cur_fp, 0x8);
		arg5 = get_mem_val(cur_fp, 0x10);
		printk("LR %llx FP %llx Args %llx %llx %llx %llx %llx\n", lr, cur_fp, arg1, arg2, arg3, arg4, arg5);
		cur_fp = get_mem_val(cur_fp, 0x0);
	} while (cur_fp != 0);

	return 0;
}
```



![](img/02-02-15-57-26.png)



![](img/02-02-15-58-10.png)