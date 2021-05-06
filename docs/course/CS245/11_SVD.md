---
title: 11 Singular Value Decomposition
date: 2021-05-06 11:18:40
tags: 
- Data Science

categories: 
- Courses

sidebar: true
lang: en-US
---


<!-- more -->


**Best fitting line**, maximize the sum of squared projections of n points to a projection $v$


### Relation with other Concepts

**Recall PCA**.  maximum variance direction: when $A$ is decentralized, then the value of SVD of A is same as PCA

**Relation to Eigen Decomposition**. $||Av||^2 = \lambda$, we are actually finding the maximal $\lambda$ (eigen value), and its corresponding eigen vector
> solution for SVD: find the maximal eigen decomposition

### Solution of SVD

> A greedy algorithm, but can find the global optimum

find a subspace (a set of orthogonal best fitting lines)

Note, when $k=r(\mathbf{A})+1$, reach null space, i.e. $\max_{v \bot v_1,\ldots, v_{k-1}, ||v||=1} ||\mathbf{Av}||^2 = 0$


### Details of SVD

- projection direction $V$
- norm of projection $D$ (diag)
- normalized projection $U$


$$
\mathbf{A} = \mathbf{UDV^T} = \sum_{i=1}^{k} d_i \mathbf{u_i v_i^T}
$$