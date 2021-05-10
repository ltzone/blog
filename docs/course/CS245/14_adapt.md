---
title: 14 Domain Adaptation
date: 2021-05-10 09:19:08
tags: 
- Data Science

categories: 
- Courses

sidebar: true
lang: en-US
---


<!-- more -->


## Traditional Era


### Projection to common subspace

> Baktashmotlagh, et al. "Unsupervised domain adaptation by domain invariant projection", ICCV 2013

> We want to learn a projection for $n_s$ source samples and $n_t$ target samples, where the samples are "closer" after projection.
>
> What is the measure of "close"? MMD (max mean distance), as a simple solution

$$
\mathbf{X}_{s}=\left[\mathbf{x}_{1}^{s}, \mathbf{x}_{2}^{s}, \ldots, \mathbf{x}_{n_{s}}^{s}\right] \quad \mathbf{X}_{t}=\left[\mathbf{x}_{1}^{t}, \mathbf{x}_{2}^{t}, \ldots, \mathbf{x}_{n_{t}}^{t}\right]
$$


$$
\begin{array}{c}
d\left(\mathbf{W}^{T} \mathbf{X}_{s}, \mathbf{W}^{T} \mathbf{X}_{t}\right)^{2}=\left\|\frac{1}{n_{s}} \sum_{i=1}^{n_{s}} \phi\left(\mathbf{W}^{T} \mathbf{x}_{i}^{s}\right)-\frac{1}{n_{t}} \sum_{i=1}^{n_{t}} \phi\left(\mathbf{W}^{T} \mathbf{x}_{i}^{t}\right)\right\|^{2} \\
=\mathrm{tr}\left(\mathbf{K}_{\mathbf{W}} \mathbf{L}\right) \\
\mathbf{K}_{\mathbf{W}}=\left[\begin{array}{ll}
\mathbf{K}_{s s} & \mathbf{K}_{s t} \\
\mathbf{K}_{t s} & \mathbf{K}_{t t}
\end{array}\right] L_{i, j}=\left\{\begin{array}{ll}
\frac{1}{n_{s}^{2}}, & \text { if } i, j \in \mathcal{S} \\
\frac{1}{n_{t}^{2}}, & \text { if } i, j \in \mathcal{T} \\
-\frac{1}{n_s {n_{t}},}, & \text { otherwise }
\end{array}\right.
\end{array}
$$


> $\phi$ is not necessary, sometimes a wise $\phi$ may help. It has been proved that can be reduced to $\mathrm{tr}\left(\mathbf{K}_{\mathbf{W}} \mathbf{L}\right)$, $\mathbf{K}$ is simply a shared kernel function for the source and target domain, $\mathbf{L}$ is an indicating matrix to simplify the expression (no actual meaning)

#### Domain Invariant Projection

DIP problem

$$
\begin{aligned}
& \min _{\mathbf{W}} & \mathrm{tr}\left(\mathbf{K}_{\mathbf{W}} \mathbf{L}\right) \\
& \text { s.t. } & \mathbf{W}^{T} \mathbf{W}=\mathbf{I} .
\end{aligned}
$$


DIP-CC problem (with class clustering constraint)

$$
\begin{array}{l}
\min _{\mathbf{W}} \quad \mathrm{tr}\left(\mathbf{K}_{\mathbf{W}} \mathbf{L}\right)+ \lambda \sum_{\mathbf{c=1}}^{\mathbf{C}} \sum_{i=1}^{n_{c}}\left\|\mathbf{W}^{T} \mathbf{x}_{i, c}^{s}-\mathbf{\mu}_{c}\right\|^{2} \\
\text { s.t. } \quad \mathbf{W}^{T} \mathbf{W}=\mathbf{I}
\end{array}
$$



After obtaining $\mathrm{W}$, use $\phi\left(\mathbf{W}^{T} \mathbf{X}_{s}\right)$ and $\phi\left(\mathbf{W}^{T} \mathbf{X}_{t}\right)$

### Transfer Component Analysis (TCA)

We still use the previous definition of "close"


$$
\begin{array}{c}
d\left(\mathbf{W}^{T} \mathbf{X}_{s}, \mathbf{W}^{T} \mathbf{X}_{t}\right)^{2}=
=\mathrm{tr}\left(\mathbf{K}_{\mathbf{W}} \mathbf{L}\right) \\
\mathbf{K}_{\mathbf{W}}=\left[\begin{array}{ll}
\mathbf{K}_{s s} & \mathbf{K}_{s t} \\
\mathbf{K}_{t s} & \mathbf{K}_{t t}
\end{array}\right] L_{i, j}=\left\{\begin{array}{ll}
\frac{1}{n_{s}^{2}}, & \text { if } i, j \in \mathcal{S} \\
\frac{1}{n_{t}^{2}}, & \text { if } i, j \in \mathcal{T} \\
-\frac{1}{n_s {n_{t}},}, & \text { otherwise }
\end{array}\right.
\end{array}
$$

Use $\tilde{K}$ to replace the original kernel $K$

$$
\mathbf{K}=\left(\mathbf{K K}^{-\frac{1}{2}}\right)\left(\mathbf{K}^{-\frac{1}{2}} \mathbf{K}\right)=\tilde{\phi}\left(\mathbf{X}_{s t}\right)^{T} \tilde{\phi}\left(\mathbf{X}_{s t}\right)
$$
Introduce transformation matrix $\tilde{\mathbf{W}}$ for fake representation $\tilde{\phi}\left(\mathbf{X}_{s t}\right)$
$$
\begin{array}{c}
\tilde{\mathbf{K}}=\left(\tilde{\phi}\left(\mathbf{X}_{s t}\right)^{T} \tilde{\mathbf{W}}\right)\left(\tilde{\mathbf{W}}^{T} \tilde{\phi}\left(\mathbf{X}_{s t}\right)\right)=\mathbf{K} \mathbf{W} \mathbf{W}^{T} \mathbf{K}, \text { in } \  \text{ which } \mathbf{W}=\mathbf{K}^{-\frac{1}{2}} \tilde{\mathbf{W}} \\
\mathrm{tr}(\tilde{\mathbf{K}} \mathbf{L})=\mathrm{tr}\left(\mathbf{K W} \mathbf{W}^{T} \mathbf{K L}\right)=\mathrm{tr}\left(\mathbf{W}^{T} \mathbf{K L K W}\right)
\end{array}
$$

The last transformation is based on the "shift invariance" property of trace.

### interpolation on the manifold


### sample selection


### domain-invariant dictionary


### low-rank reconstruction



## Early Deep Era




## GAN Era

