---
title: 6 Dimensionality Reduction
date: 2021-03-16 11:27:55
tags: 
- Data Mining

categories: 
- Courses

sidebar: true
lang: en-US
---


<!-- more -->


- In practice, Data lies on or near a low d-dimensional subspace
- Axes of the subspace are effective representation of the data
- **Goal:** Discover the axis of data


## Singular Value Decomposition


$$
A_{m\times n} = U_{m \times r} \Sigma_{r\times r}  (V_{n \times r})^T
$$

- $A$: Input Data matrix
  - m documents, n terms
  - m users, n ratings
- $U$: Left Singular Vectors 左奇异阵
  - m documents, r concepts
  - m users, r preferences
  - $U^T U = I$
- $\Sigma$: Singular Values, diagonal
  - r, strength of each concept
  - r, strength of each preference to the rating
  - ***Diagonal, positive, in increasing order***
- $V$: Right Singular Vectors，右奇异阵
  - n terms, r concepts
  - n ratings, r preferences
  - $V^T V = I$ Column Orthonormal

![](./img/03-23-10-11-09.png)

$$
\mathbf{A} \approx \mathbf{U} \mathbf{\Sigma} \mathbf{V}^{T}=\sum_{i} \sigma_{i} \mathbf{u}_{i} \circ \mathbf{v}_{i}^{\top}
$$

### Example: Users to Movies

::: tip

introduce another set of dimensions "concept", and project the samples-features into samples-concept-features.

:::

![](./img/03-23-10-14-53.png)

![](./img/03-23-10-15-04.png)

### SVD-Another View

- **Observation.** The first singular vector - the projection direction with maximum variance
  ![](./img/03-23-10-22-09.png)
  - Instead of using two coordinates $(x,y)$ to describe point locations, let’s use only one coordinate $(z)$
  - Point’s position is its location along vector $V_1$
- **Observation.** Linear combinations of movies’ ratings form a concept!
  ![](./img/03-23-10-25-13.png)
- **Observation.** $U\Sigma$ gives the coordinates of the points in the projection axis
  ![](./img/03-23-10-27-16.png)
- **Statement** (without rigorious proof): **SVD gives `best’ axis to project on minimizing the sum of reconstruction errors**
  $$
  \sum_{i=1}^{N} \sum_{j=1}^{D} \| x_{i j}-z_{i j}\|^{2}
  $$
  

### SVD in Dimensionality Reduction

Set the smallest singular values to zero!

![](./img/03-23-10-31-20.png)

![](./img/03-23-10-34-43.png)

**B approximates A!**
- i.e. B is a solution to $\min_{B} ||A-B||_F$ when rank(B) = k

How many $\sigma$s to keep?
- Rule-of-a-thumb: keep 80% to 90% of the 'energy' = $\sum_i \sigma_i^2$

### How to Compute SVD

By decompoing $A^TA$ and $AA^T$

> A is not symmetric, so we work on $A^TA$ and $AA^T$

![](./img/03-23-10-47-02.png)

How to do Eigen-Decomposition efficiently?

::: theorem

1. Start with any "guess eigenvector" $x_0$
2. Construct $x_{k+1} = \frac{Mx_k}{||Mx_k||}$ for $k=0,1,\ldots$, where $|| ... ||$ denotes the Frobenius norm
3. Stop when consecutive $x_k$ changes little
:::

![](./img/03-23-11-03-06.png)

### Complexity


- To compute SVD:
  - $O(nm^2)$ or $O(n^2m)$ (whichever is less)
- But:
  - Less work, if we just want singular values
  - if we want first k singular vectors
  - if the matrix is sparse
- Implemented in linear algebra packages like LINPACK, Matlab, SPlus, Mathematica ...
> Pay attention to the format of the return value in practice

### Case Study: Recommendation

**Idea**: **Map query into a 'concept space'**, and find similar users whose projection of ratings in the concept space is similar to the query.

If we want to find users who like Movie 1,
1. map query into concept space
   ![](./img/03-23-11-11-51.png)
2. For a fresh user d,
   ![](./img/03-23-11-12-20.png)
> User $d$ that rated 2 and 3 will be similar to query $q$ that rated movie 1, although their have zero ratings in common (may differ a lot in the original Euclidean space)


::: tip 

Convention: the right singular matrix should represent the bases of the concept space

:::
### SVD Drawbacks


- Interpretability problem:
  - A singular vector specifies a linear combination of all input columns or rows
- Lack of sparsity:
  - Singular vectors are dense


## CUR Decomposition

CUR = Column + Upper + Row

- **Sample** Columns in A to construct C
  ![](./img/03-23-11-20-56.png)
  > Note this is a randomized algorithm, same column can be sampled more than once
- **Sample** Rows in A to construct R (*sample WITH replacement*), similar as above
  > Intuition: minimize the reconstruction error
- U is the pseudo-inverse of the intersection of C & R
  1. Let $W$ be the intersection of sampled columns C and rows R. Let SVD of $W = XZY^T$
  2. Let $U = W^+ = YZ^+XT$ ($Z^+_{ii} = \frac{1}{Z_{ii}}$)
  > Why pseudo? if $W$ is nonsigulaar, pseudoinverse is the true inverse

**Conclusion**. CUR can approximate the reconstruction error, with a constant gap to SVD

### CUR Pros & Cons

Pros
- Easy interpretation 
- Sparse basis
  - Basis vectors are actual columns and rows

Cons
- Duplicate columns and rows
  - Columns of large norms will be sampled many times
- CUR produce **non-orthogonal** basis
  > But sometimes may also produce interpretable results, can be a merit!
  >
  > ![](./img/03-23-11-28-49.png)
  >
  > SVD dimensions are orthogonal CUR finds two clouds!


### SVD vs. CUR

![](./img/03-23-11-29-31.png)

A little demanding the accuracy (reconstruction error) poses will cause a great burden on time and space for SVD.

![](./img/03-23-11-31-12.png)

> CUR can also produce good results

- Reduce dimensionality for a sparse author-conference matrix: 428K authors (rows), 3659 conferences (columns)
  - Accuracy = 1 – relative sum squared errors
  - Space ratio = #output matrix entries / #input matrix entries
  - CPU time


### SVD Application - PCA

> From the algorithm's perspective, the two methods make no difference, but can provide us with a new point of view to understand SVD

**Prequisite.** Pre-process the data so that the features have the same mean (zero) and variance

![](./img/03-23-11-34-01.png)

Renormalization **rescales** the different attributes to make them more **comparable**


**Goal.** find the **principal** direction of **variation of the data**
- One way is to find the unit vector u such that the **variance** of the **projected** data to u is **maximized**.

### Solution

The length of the projection is given by $\mathrm{x}^{\top} \mathrm{u} .$ We would like to choose a unit-length u so as to maximize
$$
\begin{aligned}
\frac{1}{m} \sum_{i=1}^{m}\left(x^{(i)^{T}} u\right)^{2} &=\frac{1}{m} \sum_{i=1}^{m} u^{T} x^{(i)} x^{(i)^{T}} u \\
&=u^{T}\left(\frac{1}{m} \sum_{i=1}^{m} x^{(i)} x^{(i)^{T}}\right) u
\end{aligned}
$$


Maximizing the above subiect to $\|\mathrm{ul}\|_{2}=1$ gives the principal eigenvector of $\Sigma=\frac{1}{m} \sum_{i=1}^{m} x^{(i)} x^{(i)^{T}}$

Why principal? $\Sigma \mathrm{u}=\lambda \mathrm{u} \Leftrightarrow \mathrm{u}^{\top} \Sigma \mathrm{u}=\lambda \mathrm{u}^{\top} \mathrm{u}=\lambda$

We have found a 1-dimensional subspace to approximate the data!

### SVD & PCA


SVD: picking basis that minimizes the approximation error arising from projecting the data onto the k- dimensional subspace spanned by them

PCA: seeking the “major axis of variation” (the direction on which the data approximately lies)

> - Same if the matrix is **zero-centered**
> - Both **minimize reconstruction error**/**maximize projected variance**
> - Application differs
>   - SVD: Find the best low rank approximation
>   - PCA: Find how data varies in relationship to its mean


## Factor Analysis
