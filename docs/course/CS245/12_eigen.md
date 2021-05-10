---
title: 12 Eigenvalue Decomposition
date: 2021-05-08 09:05:47
tags: 
- Data Science

categories: 
- Courses

sidebar: true
lang: en-US
---


<!-- more -->


## Definition

- For any $\mathbf{M}_{n\times n}$, those $\mathbf{v}$ with $\mathbf{Mv}=\lambda\mathbf{v}$ are called eigenvector
- This set together with the zero vector forms a subspace, closed under addition and scalar multiplication (for same $\lambda$, equivalent to streatching the eigenvector )

### Relation to SVD

- Let $\mathbf{M} = \mathbf{A^TA}$,

Slide 3: SVD -> Eigen

Slide 4: Eigen -> SVD


## Solution of Eigen Decompositions

$Mx = \lambda x \Rightarrow (M-\lambda I)x = 0$

$(M-\lambda I)x = 0$ has non-zero solutions for $x$ iff $det(M-\lambda I) = 0$, solve the determinant equation


## Properties

- $tr(M) = \sum_{i} \lambda_i$
- $det(M) = \pi_{i} \lambda_i$


## Application


### Application 1: Priciple Component Analysis

Maximum variance direction: when $\mathbf{X}$ is decentralized
$$
\begin{array}{c}
\frac{1}{n} \sum_{i=1}^{n}\left(\mathbf{v}^{T} \mathbf{x}_{i}\right)^{2}=\frac{1}{n} \mathbf{v}^{T} \mathbf{X} \mathbf{X}^{T} \mathbf{v} \\
\max _{\mathbf{v}} \quad \mathbf{v}^{T} \mathbf{X} \mathbf{X}^{T} \mathbf{v}
\end{array}
$$
s.t. $\mathbf{v}^{T} \mathbf{v}=1$
Lagrangian form:
$$
\mathcal{L}_{\mathbf{v}}=\mathbf{v}^{T} \mathbf{X} \mathbf{x}^{T} \mathbf{v}+\lambda\left(1-\mathbf{v}^{T} \mathbf{v}\right)
$$
$$
\begin{array}{c}
\frac{\partial \mathcal{L}_{\mathrm{V}}}{\partial \mathbf{v}}=\mathbf{X X}^{T} \mathbf{v}-\lambda \mathbf{v}=0 \\
\mathbf{X X T}_{\mathbf{V}}=\lambda \mathbf{v}
\end{array}
$$
Eigen decomposition



### Application 2: Canonical Correlation Analysis


$$
\begin{array}{c}
\max _{\alpha, \beta} \frac{\sum_{i} \mathbf{\alpha}^{T} \mathbf{x}_{i} \mathbf{y}_{i}^{T} \mathbf{\beta}}{\sqrt{\left(\sum_{i} \mathbf{\alpha}^{T} \mathbf{x}_{i} \mathbf{x}_{i}^{T} \mathbf{\alpha}\right)\left(\sum_{i} \mathbf{\beta}^{T} \mathbf{y}_{i} \mathbf{y}_{i}^{T} \mathbf{\beta}\right)}} \\
\text { s.t. } \quad \frac{1}{N} \sum_{i} \mathbf{\alpha}^{T} \mathbf{x}_{i} \mathbf{x}_{i}^{T} \mathbf{\alpha}=1 \\
\frac{1}{N} \sum_{i} \mathbf{\beta}^{T} \mathbf{y}_{i} \mathbf{y}_{i}^{T} \mathbf{\beta}=1 \\
\mathcal{L}_{\alpha, \beta, \lambda_{1}, \lambda_{2}}=\sum_{i} \alpha^{T} \mathbf{x}_{i} \mathbf{y}_{i}^{T} \beta-\lambda_{1}\left(\sum_{i} \alpha^{T} \mathbf{x}_{i} \mathbf{x}_{i}^{T} \alpha-N\right)-\lambda_{2}\left(\sum_{i} \beta^{T} \mathbf{y}_{i} \mathbf{y}_{i}^{T} \beta-N\right)
\end{array}
$$


$$
\begin{array}{l}
\frac{\partial \mathcal{L}}{\partial \alpha}=\mathbf{0} \Rightarrow \sum_{i} \mathbf{x}_{i} \mathbf{y}_{i}^{T} \mathbf{\beta}=2 \lambda_{1} \sum_{i} \mathbf{x}_{i} \mathbf{x}_{i}^{T} \mathbf{\alpha} \\
\frac{\partial \mathcal{L}}{\partial \mathbf{\beta}}=\mathbf{0} \Rightarrow \sum_{i} \mathbf{y}_{i} \mathbf{x}_{i}^{T} \mathbf{\alpha}=2 \lambda_{2} \sum_{i} \mathbf{y}_{i} \mathbf{y}_{i}^{T} \mathbf{\beta}
\end{array}
$$
It can be proved that $\lambda_{1}=\lambda_{2}$ (based on the two above derivations and the original two constraints in the problem, omitted)

The above two derivations can be combined into a matrix form
$$
\left[\begin{array}{cc}
0 & \sum_{i} \mathbf{x}_{i} \mathbf{y}_{i}^{T} \\
\sum_{i} \mathbf{y}_{i} \mathbf{x}_{i}^{T} & \mathbf{0}
\end{array}\right]\left[\begin{array}{l}
\mathbf{\alpha} \\
\mathbf{\beta}
\end{array}\right]=2 \lambda\left[\begin{array}{cc}
\sum_{i} \mathbf{x}_{i} \mathbf{x}_{i}^{T} & \mathbf{0} \\
\mathbf{0} & \sum_{i} \mathbf{y}_{i} \mathbf{y}_{i}^{T}
\end{array}\right]\left[\begin{array}{l}
\mathbf{\alpha} \\
\mathbf{\beta}
\end{array}\right]
$$

$$
\left[\begin{array}{cc}
\sum_{i} \mathbf{x}_{i} \mathrm{x}_{i}^{T} & 0 \\
0 & \sum_{i} \mathrm{y}_{i} \mathbf{y}_{i}^{T}
\end{array}\right]^{-1}\left[\begin{array}{cc}
\mathbf{0} & \sum_{i} \mathbf{x}_{i} \mathbf{y}_{i}^{T} \\
\sum_{i} \mathbf{y}_{i} \mathbf{x}_{i}^{T} & \mathbf{0}
\end{array}\right]\left[\begin{array}{l}
\mathbf{\alpha} \\
\mathbf{\beta}
\end{array}\right]=2 \lambda\left[\begin{array}{l}
\alpha \\
\beta
\end{array}\right]
$$

now reduced to eigen decomposition form

