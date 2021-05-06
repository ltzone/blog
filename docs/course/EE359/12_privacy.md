---
title: 12 Differential Privacy
date: 2021-04-27 10:11:54
tags: 
- Data Mining

categories: 
- Courses

sidebar: true
lang: en-US
---

![](../../course/EE359/img/05-06-08-05-10.png)

- Basic idea: 
  - use a random algorithm that provides deniable possibility to ensure privacy

- Measure: 
  - max divergence (defined as log probability ratio)

- Basic Mechanisms:
  - Randomized response (by throwing a coin)
  - Laplace
  - Gaussian
  - Exponential


<!-- more -->


## Background

- AOL Search Debacle
- Netflix competition
> **Anonymity is NOT enough! Linkage Attack**
> 
> High-dimensional data is unique


No more dataset, only Release Statistics?
- Not release dataset. How about releasing statistics? 
- Can the statistics be used to track an individual?
  > Statistics on small datasets is unsafe!
  > 
  > ![](./img/04-27-10-28-22.png)
  > 
  > Correlation among different SNPs, Alice’s DNA reveals: If Alice is in the Cancer set or Healthy set



### Summary

- Anonymization may not work
  - identify an individual by collection of fields, attributes, zip code, date of birth, sex ...
  - A **linkage attack** to match “anonymized” records with non- anonymized records
- Re-Identification may not be the only risk
  - A collection of **medical records** on a given date list a **small number** of diagnoses. Additional information of visiting the facility on the date **narrows range** of possible diagnoses
- Queries over **large sets** may be risky
  - **differencing** attack to two large sets,one w/X,one w/oX

- Summary statistics may be risky
  - Compute frequencies of DNA sequences: AAGGCTAA and ATGGCTAA in a reference population
  - Observe **frequencies differ** for a subpopulation with a disease
  - Given the genome data of an individual, possible to determine if the individual has the disease 
- “Ordinary” facts are not OK
  - Mr. T regularly buys bread over years until suddenly switching to rarely buying bread — most likely be diagnosed with diabetes
- “Just a few” is not OK
  - **Outliers** may be more important!


## Definitions and Properties

**Definition**. Differential Privacy - Participation of a person does not change outcome

![](./img/04-27-10-40-31.png)

> Whoever is Alice or Bob in the dataset won't affect the outcome


**Solution**. Randomness
- **Randomness**: Added by randomized algorithm A 
- **Closeness**: Likelihood ratio at each point bounded
  > so that dataset is still useful


### Basic Terms

> What's our goal?

- A trustworthy **curator** holds data of individuals in database D
  > 值得信任的数据托付源
- Each row corresponds to an **individual**
- Goal: Protect every individual row while permitting statistical analysis of D
  - Non-interactive model: Curator releases *summary statistics*, or “sanitized database” once and for all
  - Interactive model: permit asking queries *adaptively*, decide which query to ask next based on observed responses

- **A privacy mechanism** is an algorithm that takes as input a database, the set of **all possible database rows, random bits, a set of (non/interactive)queries**, and produces **an output string**.

> What's privacy

- Privacy: data analysis *knows no more about an individual* after analysis is completed than before the analysis was begun
- Formally, adversary’s **prior** and **posterior** views about an individual should not be “too different”
- Reminiscent（类比） of **semantic security** for a cryptosystem:

::: details semantic security 语义安全

semantic security says nothing is learned about the plaintext（明文） from the ciphertext（密文）

![](./img/04-27-11-03-45.png)

-  if side information says the ciphertext is an encryption of “dog” or “cat,” the ciphertext leaks nothing about which of “dog” or “cat” has been encrypted
-  Adversary **simulator** has the same odds of guessing as does the **eavesdropper**(窃听者)

Most cypher tools are based upon semantic security

:::

::: tip Difference between semantic security and privacy
- Semantic security
 - 3 parties: message sender, receiver, eavesdropper
- Privacy
 - 2 parties: curator & data analyst
 - **data analyst can be adversary** (at the same time, user)
 - given as auxiliary information the encryption of a secret using random pad, the analyst can decrypt the secret, but the adversary simulator learns nothing
 - need to careful in deciding “reasonable” auxiliary knowledge
> even harder! we need to provide information, while still be adversary
:::

> There goes the definition of privacy

- “Privacy” comes from plausible deniability of any outcome. Report if one has property P by:
  1. Flip a coin
  2. If **tails**, then report truthfully
  3. If **heads**, then flip a second coin and report “Yes” if heads and “No” if tails
- What is the expected number of “Yes”?
  - The expected number of “Yes” is 1/4 × total no. of participants “who do not has P” + 3/4 × total no. of participants “who has P”
  - if p is the true fraction of having P, the expected number of “Yes” is (1/4) + p/2

> Now, it doesn't make sense to infer the P property of a single user from a single observation.
> 
> But globally, we can still have an insight of the group's property P
> 
> "plausible deniability", we can reasonably deny an observation

### Randomized Algorithm

**Probability Simplex**: given a discrete set $\mathrm{B}$, the probability simplex over $\mathrm{B}$, denoted $\Delta(\mathrm{B})$ is defined to be
$$
\Delta(B)=\left\{x \in \mathbb{R}^{|B|}: x_{i} \geq 0 \text { for all } i \text { and } \sum_{i=1}^{|B|} x_{i}=1\right\}
$$

**A randomize alg**. $\mathcal{M}$ with domain $\mathrm{A}$ and discrete range $\mathrm{B}$ is associated with a mapping: $A \rightarrow \Delta(B) .$ On input $a \in A$, alg. $M$ outputs $\mathcal{M}(\mathrm{a})=\mathrm{b}$ with probability $(\mathrm{M}(\mathrm{a})) \mathrm{b}$ for each $\mathrm{b} \in \mathrm{B}$
> Note $b$ can take over $\Delta(B)$

**Distance between databases**: the 11 -norm of a database $\mathrm{X}$ is $\|\mathrm{X}\|_1$. The 11 distance between $X$ and $Y$ is $\|X-Y\|_1$
- a measure of how many records differ between X \& Y
> Other alternative distances are also OK


### Differential Privacy

Assume distr with Alice is $D$, with Bob is $D'$., after the algorithm $A$, we expect ...

![](./img/04-27-11-19-51.png)

For all D, D' that differ in one person's value, If $\mathrm{A}=\epsilon$ -differentially private randomized algorithm, then:
Max-divergence of p(A(D)) and p(A(D')) is 

$$
\left.\sup _{t}\left|\log \frac{p(A(D)=t)}{p\left(A\left(D^{\prime}\right)=t\right)}\right|\right. \leq \epsilon
$$


Sometimes, we loose the condition by limiting the evalutation domain with $\delta$


If $\mathrm{A}=(\epsilon, \delta)$ -differentially private randomized algorithm, then:
$$
\max _{S, \mathrm{Pr}(A(D) \in S)>\delta}\left[\log \frac{\mathrm{Pr}(A(D) \in S)-\delta}{\mathrm{Pr}\left(A\left(D^{\prime}\right) \in S\right.}\right] \leq \epsilon
$$

The choice of $\varepsilon, \delta:$
- $\varepsilon$ should be small that an adversary cannot distinguish which is true database on the basis of observing outputs
- $\delta$ are less than the inverse of any polynomial in the size of the database
  > so that "just a few is not OK"


Given an output $\xi \sim M(x)$, privacy loss is defined as
$$
\mathcal{L}_{\mathcal{M}(x) \| \mathcal{M}(y)}^{(\xi)}=\ln \left(\frac{\mathrm{Pr}[\mathcal{M}(x)=\xi]}{\mathrm{Pr}[\mathcal{M}(y)=\xi]}\right)
$$

- `>0`, if an event is more likely under x than under y
- `<0`, otherwise

> Splitting the definition above, (by taking out $\ln$), we can now formally define differential privacy


**Definition**. A randomized alg. $\mathrm{M}$ with domain $\mathrm{X}$ is $(\varepsilon, \delta)$ -differentially private if for all $\mathrm{O} \subseteq \mathrm{Range}(\mathcal{M})$ and for all $\mathrm{x}, \mathrm{y} \in \mathrm{X}$ such that $\|\mathrm{x}-\mathrm{y}\|_{1} \leq 1$ :
$$
\mathrm{P}[\mathcal{M}(\mathrm{x}) \in \mathrm{O}] \leq \mathrm{e}^{\varepsilon} \mathrm{P}[\mathcal{M}(\mathrm{y}) \in \mathrm{O}]+\mathbf{\delta}
$$

- for every **arbitrary** pair of neighbouring databases x, y, the **posterior** distributions should be close
- $\delta$: residual probability, should be small

### An Intuitive View, Utility of above definition

- Consider differential privacy at a level of **individuals**
  - insensitive to the **addition** or **removal** of any individual
  - e.g., a differentially private movie recommendation system:
    - **Event level**: hiding the rating of a single movie, but not one’s preference for the romantic movies
    - **User level**: hiding an individual’s entire ratings
- Protection against arbitrary risks including re-identification
- Automatic neutralization of linkage attacks
- Quantification of privacy loss, allows comparisons among different techniques
  > w.r.t. semantic security


### Properties


1. Post-Processing:
  Let $\mathcal{M}$ be a randomized alg. that is $(\varepsilon, \delta)$ -differentially private. Let be an arbitrary randomized mapping. Then $f \circ \mathcal{M}$ is $(\varepsilon, \delta)-$ differentially private

  Proof: for any pair of neighboring databases $\mathrm{x}, \mathrm{y}$, and fix any event $S \subseteq R^{\prime} .$ Let $T=\{r \in R: f(r) \in S\} .$ We have

  $$
  \begin{aligned}
  \mathrm{Pr}[f(\mathcal{M}(x)) \in S] &=\mathrm{Pr}[\mathcal{M}(x) \in T] \\
  & \leq \exp (\epsilon) \mathrm{Pr}[\mathcal{M}(y) \in T]+\delta \\
  &=\exp (\epsilon) \mathrm{Pr}[f(\mathcal{M}(y)) \in S]+\delta
  \end{aligned}
  $$

2. Composition:
   - The composition of two $(\varepsilon, 0)$ -differentially private mechanisms is $(2 \varepsilon, 0)$ -differentially private
   - Composition of k differentially-private mechanisms where the i-th mechanism is $\left(\varepsilon_{i}, \delta_{i}\right)$ -differentially private, is $\left( \Sigma \varepsilon_{i},  \Sigma \delta_{i}\right)-$differentially private
3. Group privacy for $(\varepsilon, 0)$ -differentially private mechanisms:
   - Any $(\varepsilon, 0)$ -differentially private mechanism $\mathcal{M}$ is $(\mathrm{k} \varepsilon, 0)-$ differentially private for groups of size $\mathrm{k}$




## Basic Mechanisms

### Example: Coin Flipping (Randomized Response)

- Recall
  1. Flip a coin
  2. If **tails**, then report truthfully
  3. If **heads**, then flip a second coin and report “Yes” if heads and “No” if tails
- The above mechanism is ($\ln 3, 0)$-differentially private
  ![](./img/04-27-11-34-17.png)
  > all the ratio in the probability space leads to 3, so that max of all ratios is also 3

Strategies like these are called **Randomized Response**


## Illustration of Global Sensitivity: Laplace Mechanism


### Global Sensitivity

**Definition**. Global sensitivity. Given function f, sensitive dataset D

![](./img/04-27-11-37-34.png)

> D' and D only differ in one data sample, f(D) can be the mean data points in D, f should be considered as a query

> Is a differentially-private approximation to f(D)


Suppose we are Counting queries “How many elements in the database satisfy
Property P?” and that the randomeness of the algorithm comes from Laplace distribution

l1-sensitivity of counting query f:
$$
\Delta f=\max _{x, y \in \mathbb{N}^{|\mathcal{X}|} \|x-y\|_{1}=1}\|f(x)-f(y)\|_{1}=1
$$

> because at most one sample may change, 

> The sensitivity of f gives an upper bound on **how much we must perturb** output to preserve privacy (最多可能要付出的代价)

::: theorem Laplace Disribution

Laplace Distribution with scale b is the distribution with PDF:

$$
\mathrm{Lap}(x \mid b)=\frac{1}{2 b} \exp \left(-\frac{|x|}{b}\right)
$$

![](./img/05-06-08-14-47.png)

> We use Laplace distribution to add a noise to the output of $f$.
>
> as long as the mean of the distr is zero, it will not cause bias
:::


Given query f, Laplace mechanism is defined as:

$$
M(x, f(\cdot), \varepsilon)=f(x)+Y
$$

where $Y$ is a random variable drawn from $\mathrm{Lap}(\Delta f / \varepsilon)$

**Theorem**. The above mechanism is $(\varepsilon, 0)$ -differentially private

**Proof**: Let $\mathrm{px}$ denote the $\mathrm{PDF}$ of $\mathrm{M}(\mathrm{x})$ and $\mathrm{p}_{\mathrm{y}}$ denote the PDF of $\mathcal{M}(\mathrm{y})$.

at some arbitrary point $\mathrm{z}$ :
$$
\begin{array}{ll}
\frac{p_{x}(z)}{p_{y}(z)}=\frac{\exp \left(-\frac{\epsilon|f(x)-z|}{\Delta f}\right)}{\exp \left(-\frac{\epsilon|f(y)-z|}{\Delta f}\right)}&=\exp \left(\frac{\epsilon(|f(x)-z|-|f(y)-z|)}{\Delta f}\right) (def Of Laplace)\\
&\leq \exp \left(\frac{\epsilon|f(x)-f(y)|}{\Delta f}\right) (Triangle)\\
 & \leq \exp (\epsilon) (def Of GS)
\end{array}
$$


### Accuracy Loss

> Critical Question: how to avoid the case where we gives large noise

- How much noise do we introduce in Laplace mechanism?

- Let query f map databases to k numbers. $y = M(x, f(\cdot), \epsilon) = f(x) + Y$.
For $\delta \in (0, 1]$:

$$
\begin{aligned}
\mathrm{Pr}\left[\|f(x)-y\|_{\infty} \geq \ln \left(\frac{k}{\delta}\right) \cdot\left(\frac{\Delta f}{\varepsilon}\right)\right] &=\mathrm{Pr}\left[\max _{i \in \mid k]}\left|Y_{i}\right| \geq \ln \left(\frac{k}{\delta}\right) \cdot\left(\frac{\Delta f}{\varepsilon}\right)\right] \\
& \leq k \cdot \mathrm{Pr}\left[\left|Y_{i}\right| \geq \ln \left(\frac{k}{\delta}\right) \cdot\left(\frac{\Delta f}{\varepsilon}\right)\right] \\
&=k \cdot\left(\frac{\delta}{k}\right) \\
&=\delta
\end{aligned}
$$

> By Markov inequality: If Y~Lap(b), then Pr[ |Y| >= t·b ] = exp(-t)


> We restrict a range of $\ln \left(\frac{k}{\delta}\right) \cdot\left(\frac{\Delta f}{\varepsilon}\right)$, we see that the probability of large accuracy loss is bounded by a constant $\delta$, for higher accuracy, we can simply take $k$ larger numbers

### Example

- We wish to calculate which first names, from a list of 10,000 potential names, were the most common
- Query $f: N^{|X|} \rightarrow R^{10000}$
- Sensitivity $\Delta f=1$, since every person can only have at most one first name
- Calculate the frequency of all 10,000 names with $(1,0)$ -differential privacy
- With probability $95 \%$, no estimate will be off by more than an additive error of $\ln (10000 / .05) \approx 12.2$
  > in other words, $> 5 \%$ probability that the difference of the masked query result and the true result is larger than $12.2$


## Another strategy:  Gaussian Mechanism

Global Sensitivity of $f$ is $\Delta f=\max _{\mathrm{dist}\left(D, D^{\prime}\right)=1} \| f(D)-f\left(D^{\prime}\right)\|$

Output $M(D)+Z$ where
$$
Z \sim \frac{\Delta f}{\epsilon} \mathcal{N}(0,2 \ln (1.25 / \delta))
$$

We can prove that  this is $(\epsilon, \delta)$-differentially private


## Exponential Mechanism

> Before we are adding noise to the dataset, but some data can be very vulnerable to noises, example:

- We wish to choose the “best” response but adding noise directly to the computed quantity can destroy its value
  - Suppose we have an abundant supply of goods and 4 bidders: A,B,C,D, where A,B,C each bid $1.00 and D bids $3.01. What is the optimal price? At $3.01 the revenue is $3.01, at $3.00 the revenue is $3.00, but at $3.02 the revenue is 0!

- **Solution**. Exponential mechanism is defined w.r.t. **utility** function, mapping outputs to utility scores

- We only care about the sensitivity of u:
  $$
  \Delta u \equiv \max _{r \in \mathcal{R}} \max _{x, y:\|x-y\|_{1} \leq 1}|u(x, r)-u(y, {r})|
  $$
  where r is possible output
- Exponential mechanism: outputs $r \in R$ with prob. proportional to
  $$
  \exp \left(\frac{\varepsilon u(x, r)}{2 \Delta u}\right)
  $$

**Theorem**. Exponential mechanism preserves $(\varepsilon, 0)$ -differential privacy
**Proof**: The privacy loss is
$$
\begin{array}{l}
\ln \frac{\mathrm{Pr}\left[\mathcal{M}_{E}(x, u, \mathcal{R})=r\right]}{\mathrm{Pr}\left[\mathcal{M}_{E}(y, u, \mathcal{R})=r\right]}= \\
\left.\ln \left(\frac{\exp (\varepsilon u(x, r) / \Delta u)}{\exp (\varepsilon u(y, r) / \Delta u)}\right)=\varepsilon[u(x, r)-u(y, r)] / \Delta u\right) \leq \varepsilon
\end{array}
$$



**Application**. Develop on sensitive dataset for specific tasks:

- Given function f(w, D), Sensitive Data D
- Find differentially private approximation to (e.g. $w^{*}$ can be considered as max-log-likelihood) 
  $$
  w^{*}={\mathrm{argmax}}_{w} f(w, D)
  $$
- Example: $\mathrm{f}(\mathrm{w}, \mathrm{D})=$ accuracy of classifier $\mathrm{w}$ on dataset $\mathrm{D}$


- Suppose for any w,
  $$
  \left|f(w, D)-f\left(w, D^{\prime}\right)\right| \leq S
  $$
- when D and D' differ in I record. Sample w from
  $$
  p(w) \propto e^{\epsilon f(w, D) / 2 S}
  $$
  > note we use $\propto$ instead of $=$, needs normalizing
- for $\epsilon$ -differential privacy.


![](./img/05-06-08-45-39.png)

> idea somehow works like "softmax"


### Example: Parameter Tuning

Given validation data D, k classifiers w $1, \ldots$, Wk, privately find the classifier with highest accuracy on D
Here, $f(w, D)=$ classification accuracy of $w$ on $D$. For any $w$, any $D$ and D' that differ by one record
$$
\left|f(w, D)-f\left(w, D^{\prime}\right)\right| \leq \frac{1}{|D|}
$$
So, the exponential mechanism outputs $w_{i}$ with prob:
$$
\operatorname{Pr}\left(w_{i}\right) \propto e^{\epsilon|D| f\left(w_{i}, D\right) / 2}
$$



> For larger size of $D$, we have a "steeper" distribution of $w$, with smaller $\epsilon$ (privacy level), "steeper" distribution of $w$

### Compositions

omitted