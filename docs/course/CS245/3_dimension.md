---
title: 3 Curse of high-dimension
date: 2021-03-01 09:16:13
tags: 
- Data Science

categories: 
- Courses

sidebar: true
lang: en-US
---


<!-- more -->


“Curse of dimensionality” was first used by R. Bellman in the introduction of his book “Dynamic programming” in 1957

## Curse of Dimensionality

1. storage cost and time cost
2. Require more training samples to fill in the space
   > Assume every dimension has k regions, then at least $k^n$ samples are required to cover all the space
   >
   > ![](./img/03-01-09-22-49.png)
   >
   > In practice, only critical space regions will be covered
3. From another perspective, feature dimension represents model complexity.


## Overfitting and Underfitting   
High model complexity, few training samples - **overfitting** 
> the model fit the samples too much, can only fit training set but not testing set
- We see that the model fit the training set well, but bad at testing set

Low model complexity, abundant training samples - **underfitting**
> the model is intrinsically unable (a not very expressive model) to fit so many samples
- We see that the model is unable to fit the training set


| Under-fitting  | Overfitting |
| -------------  | ----------- |
| ![](./img/03-01-09-28-45.png) | ![](./img/03-01-09-28-54.png) |
| a simple model, linear, but unfer fitting for abundant traning samples | a powerful model, but unable to discriminate between boundaries due to few samples,  |


![](./img/03-01-09-31-49.png)


With fixed number of training samples, **high dimension can easily cause overfitting**.

![](./img/03-01-09-35-20.png)

> A similar figure can be obtained when 
> - fixed training sample numbers and dimensions, the performance is evaluated w.r.t. the training time.
>   - which leads to a training strategy - **early stopping**
> - fixed feature dimensions, the performance is evaluated w.r.t. how "small" the number of samples are 