---
title: 15 Streaming Algorithms
date: 2021-05-20 08:05:40
tags: 
- Data Mining

categories: 
- Courses

sidebar: true
lang: en-US
---

<!-- more -->

## Data Streams

- Data stream: sequence of signals

  - infinite
  - non-stationary (不稳定) (may not conform to iid)

- The stream model

  - elements/tuplesat a rapid rate
  - the system cannot store the entire stream

  ![image-20210520081221402](./img/15_stream/image-20210520081221402.png)

- Query

  - Standing queries: system internal

  - Adhoc queries: required by users

    > Murphy: minor error can be tolerated, better than working for a long time for nothing

- Storage

  - Archival Storage (Disk)

    > long accessing time, 
    >
    > for offline data processing, if the query is not very urgent, so that map-reduce can be used

  - Limited Working Storage (Memory)

### Applications

- **Mining Network Streams**

  - finding abnormal patterns

  - filtering out spam calls

  - detect denial-of-service attacks in IP packet streams

    > "DOS" attacks. attackers flood the server by sending a lot of requests

- **Mining Internet**

  - Query Systems: frequent trend today
  - Click Systems: detect unusual number of hits in past hour
  - Social Network News Feeds: Weibo trending topics

### Requirements

1. Types of queries one wants on answer on a data stream (element):
   - Sampling data from a stream, to construct a random sample
   - Filtering a data stream, select elements with property X
2. Types of queries one wants on answer on a data stream (statistics):
   - Queries over sliding windows, e.g. number of items of type X
   - Counting distinct elements, e.g. number of distinct items in last k elements
   - Finding frequent elements, e.g. estimate most frequent items in last k
   - Estimating moments, e.g. estimate avg./std. dev. of last k elements.

> Complicated queries can be handled over to offline systems, and users may expect a longer latency

## Sampling a fixed-size sample

**Suppose** we need to maintain a random sample S of size exactly s tuples

**Goal**: sample each item  in the sample S seem so far with *equal prob.* $s/n$.

**Problem**. at which prob to sample and at which prob to replace

::: theorem

**Algorithm**.

1. Store all the first s elements of the stream to S
2. Suppose we have seen n-1 elements, and now the nth element arrives (n **>** s)
3.  With probability s/n, keep the nth element, else discard it
4. If we picked the nth element, then it replaces one of the s elements in the sample S, picked uniformly at random

:::

### Proof

**Claim.** After n elements, the sample contains each element seen so far with probability s/n

1. Base case: After we see **n=s** elements the sample **S** has the desired property 
   - Each out of **n=s** elements is in the sample with probability s/s = 1
2. **Inductive hypothesis:** After n elements, the sample S contains each element seen so far with prob. s/n
3. **Inductive step:** For new element, clearly prob.= $s/(n+1)$
   For elements already in S, probability that the algorithm keeps it in S is: $Pr(a\in S_{n+1} | a\in S_n) =$
   ![image-20210520083952509](./img/15_stream/image-20210520083952509.png)
   - so at time n, tuples in S were there with prob s/n
   - time n->n+1, tuple stay with prob n/n+1
   - so at time n+1, tuple in S prob = s/n+1

## Filtering Data Streams

### Applications

- Spam filtering
- Publish-subscribe systems

> know whether the new element satisfies a condition

### First Cut Solution

- $O(1)$ algorithm to determine whether a new element is in the set
  - constant time, error may occur
- **Solution:**
  - Given a set of keys $S$ we want to filter
  - Create a bit array B of n bits, initially all 0s.
  - Choose a hash function h with range [0,n]
  - Hash each member of $s\in S$ to one of the n buckets, and set that bit to 1. i.e. `B[h[s]]:=1`
  - Hash each element a of the stream and output only those that hash to bit that was set to 1, i.e. Output `a` if `B[h[a]]==1`

- Creates **false positives** but **no false negatives**
  - If the item is in S we surely output it, if not we may still output it

- **Example**.

  - |S|= 1 billion email addresses

  - |B|= 8 billion bits = 1GB, for the hash values

  - **NO FN:** If the email address is in S, then it surely hashes to a bucket that has the big set to **1**, so it always gets through

  - **FP**:  Approximately 1/8 of the bits are set to 1, so about 1/8 of the addresses not in S get through to the output

    > Might less than 1/8 because the hash process itself may cause duplicate hits to same bucket

- **Analysis**. more accurate analysis for FP (rate of hashed bucket) using *throwing darts* as example

  - Consider: If we throw m darts into n equally likely targets, what is

    the probability that a target gets at least one dart?

    - Analogy: target ~ bits/buckets, darts ~ hash value of items

  - We have m darts (emails), n targets (buckets)

  - What is the probability that **a target gets at least one dart**?

    ![image-20210520090735151](./img/15_stream/image-20210520090735151.png)

  - $\rightarrow 1 - e^{-m/n}$

  - For the above example $1-e^{-1/8} = 0.1175$

    >  How to further **improve** this false positive probability? 

    >  Similar to LSH: Bloom Filter.
    >
    > Idea: making the Jaccard similarity curve from a straight line to curve by repeating

### Bloom Filter

> Intuition: throw the dart for k times, filter only if k hash values match

- **Solution:**
  - Given a set of keys $|S| = m$ we want to filter
  - Create a bit array $|B| = n$ bits, initially all 0s.
  - Choose $k$ hash function h with range [0,n]
  - Hash each member of $s\in S$ to one of the n buckets, and set that bit to 1. i.e. `B[h_i[s]]:=1`(for each i=1,...,k)
  - Hash each element a of the stream and output only those that hash to bit that was set to 1, i.e. Output `a` if `B[h_i[a]]==1` for all i = 1,...k

- **Analysis.**

  - Throwing $k\cdot m$ darts at $n$ targets

  - So fraction of 1s is $(1-e^{-km/n})$

    > The k here seems to making the prob higher
    >
    > Note, this is not the FP rate we want! Because the judging criteria is also higher.

  - But we have $k$ independent hash functions, so FP prob.is $(1-e^{-km/n})^k$

  - ![image-20210520091805727](./img/15_stream/image-20210520091805727.png)

  - For the above case, we can minimize the FP rate using 6 functions to 2.3% FP rate

- **Summary.**

  - Bloom filters guarantee **no false negatives**, and use limited memory
    - Great for pre-processing before more expensive checks
  - Suitable for **hardware implementation (even faster)**
    - Hash function computations can be parallelized
  - Is it better to have **1** big **B** or k small **B**s? 
    - **It is the same:** $(1 – e^{-km/n})^k$ vs. $(1 – e^{-m/(n/k)})^k$
    - But keeping **1 big B** is **simpler**
  - Disadvantage: only insertion, no deletion from Bloom Filter.
    - Deleting bucket may cause FN!

## Count-Min Sketch

- Faced with big data streams, storing all elements and corresponding frequencies is **impossible**.
  - **Approximate** counts are acceptable. 
  - We can use **hashing** again.

> Unlink filtering, now we need to count the elements

- Simple Solution:
  - **Initialization:** `count[i] = 0` for all `i=1,...,w`
  - **Increment**: `count[h(a)] += 1`
  - **Retrieve** `return count[h(a)]`
  - ![image-20210520092951653](./img/15_stream/image-20210520092951653.png)
- More Hash functions
  - We use d pairwise independent hash functions
  - **Increment** count of element a `count[i,h_i(a)] += 1` for all `i=1,...,d`
  - **Retrieve** `return min(count[i,h_i(a)])`
  - ![image-20210520092944437](./img/15_stream/image-20210520092944437.png)

- Guarantees

  - Theorem[1]: with probability $1-\delta$, the error is at most $\varepsilon *$ count . Concrete values for these error bounds can be chosen by setting $w=\left[\frac{e}{\varepsilon}\right]$ and $\mathrm{d}=\left[\ln \left(\frac{1}{\delta}\right)\right], \mathrm{e} \approx 2.718$

  - Adding another **hash** function **exponentially** decreases the chance of hash conflicts

    > corresponds to repeated experiments

  - Increasing the **width** helps spread up the counts with a **linear** effect