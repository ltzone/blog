---
title: 10 Correlation and Causation
date: 2021-04-29 10:08:26
tags: 
- Data Science

categories: 
- Courses

sidebar: true
lang: en-US
---


<!-- more -->


## Correlation

### Co-occurrence

$x = [x_1,x_2,\ldots,x_n]$, $y = [y_1,y_2,\ldots,y_n]$, $S = \{(x_1,y_1),\ldots, (x_n,y_n)\}$

e.g. x is height of n students, y is weight of n students, or, x and y are two pictures, $x_n$, $y_n$ are value of features

How many times $x'$ and $y'$ co-occur in S?

### Frequent Itemset

Problem. frequency of (a,b) co-occur in a transaction

Definitions.
- Itemset
- Support of X, frequency of an itemset X
- frequent itemset, if support $\ge$ threshold

Solution. [Apriori Algorithm](../EE359/10_freqitem#Apriori)


### Correlation

$$
corr(\mathbf{x},\mathbf{y}) = \frac{cov(\mathbf{x},\mathbf{y})}{\sigma_x\sigma_y}
$$

### Canonical Correlation Analysis


> What if each sample is a vector instead of a scalar? Dataset: $\mathbf{X},\mathbf{Y}$
>
> e.g. $X = [\mathbf{x}_1, \mathbf{x}_2,\ldots, \mathbf{x}_n]$, $Y = [\mathbf{y}_1, \mathbf{y}_2,\ldots, \mathbf{y}_n]$, where $\mathbf{x}_1$ represents visual feature of video1, $\mathbf{y}_1$ represents audio feature of video1.



1. Decentralize $X$ and $Y$.
2. Learn projection $w_x$ and $w_y$ to maximize the correlation between X and Y.

$$\tilde{X} = \mathbf{w}_{x,1\times d}^T \mathbf{X}_{d\times n}, \tilde{Y} = \mathbf{w}_y^T \mathbf{Y}$$

3. then we can use the correlation in the previous section

$$
\max _{{\mathbf{\tilde{X}}}, \tilde{\mathbf{Y}}} \frac{\tilde{\mathbf{X}} \tilde{\mathbf{Y}}^{T}}{\sqrt{\left(\tilde{\mathbf{X}} \mathbf{X}^{T}\right)\left(\tilde{\mathbf{Y}} \mathbf{Y}^{T}\right)}} \quad \Longrightarrow \max _{\mathbf{w}_{x}, \mathbf{w}_{y}} \frac{\mathbf{w}_{x}^{T} \mathbf{X} \mathbf{Y}^{T} \mathbf{w}_{y}}{\sqrt{\left(\mathbf{w}_{x}^{T} \mathbf{X} \mathbf{X}^{T} \mathbf{w}_{x}\right)\left(\mathbf{w}_{y}^{T} \mathbf{Y} \mathbf{Y}^{T} \mathbf{w}_{y}\right)}}
$$

### Kernel Canonical Correlation Analysis (KCCA)

> What if each sample is a vector with infinite dimension?
> 
> Kernel method, representation theorem

$\phi(X) = [\phi(x_1),\ldots,]$


For $\phi(\mathbf{X})$ and $\phi(\mathbf{Y})$, we cannot use $\mathbf{w}_{x}$ and $\mathbf{w}_{y}$
Representation theorem: $\mathbf{w}_{x} \leftarrow \phi(\mathbf{X}) \boldsymbol{\alpha}_{x}, \mathbf{w}_{y} \leftarrow \phi(\mathbf{Y}) \boldsymbol{\alpha}_{y}$
$$\max _{\mathbf{w}_{x}, \mathbf{w}_{y}} \frac{\mathbf{w}_{x}^{T} \phi(\mathbf{X}) \phi(\mathbf{Y})^{T} \mathbf{w}_{y}}{\sqrt{\left(\mathbf{w}_{x}^{T} \phi(\mathbf{X}) \phi(\mathbf{X})^{T} \mathbf{w}_{x}\right)\left(\mathbf{w}_{y}^{T} \phi(\mathbf{Y}) \phi(\mathbf{Y})^{T} \mathbf{w}_{y}\right)}}$$


$$
\begin{aligned}
\max _{\alpha_{x}, \alpha_{y}} & \frac{\boldsymbol{\alpha}_{x}^{T} \phi(\mathbf{X})^{T} \phi(\mathbf{X}) \phi(\mathbf{Y})^{T} \phi(\mathbf{Y}) \boldsymbol{\alpha}_{y}}{\sqrt{\left(\boldsymbol{\alpha}_{x}^{T} \phi(\mathbf{X})^{T} \phi(\mathbf{X}) \phi(\mathbf{X})^{T} \phi(\mathbf{X}) \boldsymbol{\alpha}_{x}\right)\left(\boldsymbol{\alpha}_{y}^{T} \phi(\mathbf{Y})^{T} \phi(\mathbf{Y}) \phi(\mathbf{Y})^{T} \phi(\mathbf{Y}) \alpha_{y}\right)}} \\
&=\frac{\boldsymbol{\alpha}_{x}^{T} K(\mathbf{X}) K(\mathbf{Y}) \boldsymbol{\alpha}_{y}}{\sqrt{\left(\boldsymbol{\alpha}_{x}^{T} K(\mathbf{X}) K(\mathbf{X}) \alpha_{x}\right)\left(\alpha_{y}^{T} K(\mathbf{Y}) K(\mathbf{Y}) \alpha_{y}\right)}}
\end{aligned}
$$

### Misc

- Independence, $p(x,y)=p(x)p(y)$
  -  $\Rightarrow$ Uncorrelation ($E(X)E(Y)=E(XY)$)
- Conditional Independence $x \bot y | z$
  - $p(x,y|z)=p(x|z)p(y|z)$,
  - $p(x|y,z) = p(x|z)$


## Causation




