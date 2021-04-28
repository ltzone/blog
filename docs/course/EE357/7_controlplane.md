---
title: Chapter 5 - Network Layer (Control Plane)
date: 2021-04-21 11:28:05
tags: 
- Computer Networks

categories: 
- Courses

sidebar: true
lang: en-US
---


<!-- more -->

Recall: two network-layer functions:
- forwarding: move packets from router’s input to appropriate router output
**data plane**
- routing: determine route taken by packets from source to destination **control plane**


Two approaches to structuring network control plane:
- per-router control (traditional)
- logically centralized control (software defined networking)

## Routing Protocols

**Goal.** determine good paths/routes from sending hosts to receivers, through network of routers

- path: sequence of routers packets will traverse in going from given initial source host to given final destination host
- “good”: least “cost”, “fastest”, “least congested”
- routing: a “top-10” networking challenge!



### Link State

AKA [Dijkstra's Algorithm](../CS222/0928_greedy.md#dijkstra-s-algorithm), omitted, 
- need to have the complete network topology 
- should know all the costs in the network.

> To implement, every node will flood its costs to its neighbors so that everyone in the network can know the topology and link costs.

- computes least cost paths from one node (‘source”) to all other nodes
  - gives forwarding table for that node
- iterative: **after k iterations**, know least cost path to k dest.’s


::: tip Discussion

$O(n\log n)$ complexity for n nodes

> - Initially, all nodes send to their nearest, while c choose randomly between B and D to send
> - "link cost equals amount of carried traffic", We have got a node cost shown in the first figure
> - now the original graph is no longer the shortest path, we have got a shortest path shown in figure 2.


![](./img/04-28-10-20-30.png)


**Issue: osciliation** Now freqeunt switching causes great overhead.

> Tentative solution: async-ly updating forwarding table
:::


### Distance Vector


AKA [Bellman-Ford](../CS222/1019_dp2.md#bellman-ford) equation (dynamic programming)


![](./img/04-28-10-27-37.png)

- $D_{x}(y)=$ **estimate** of least cost from $x$ to $y$
  > in fact, should never be accurate
  - $x$ maintains distance vector $D_{x}=\left[D_{x}(y): y \in N\right]$ 
- node x:
  - knows cost to each neighbor $v: c(x, v)$
  -  **maintains its neighbors' distance vectors**. For each neighbor $\mathrm{v}, \mathrm{x}$ maintains $D_{v}=\left[D_{v}(y): y \in N\right]$
  > also need to store neighbors' distance neighbors
  > - together, a table of (self + neighbors) * all nodes dist vector


key idea:
- from time-to-time, each node sends its own distance vector estimate to neighbors
- when $x$ receives new DV estimate from neighbor, first store it down, then it updates its own DV using B-F equation:
  
  $D_{x}(y) \leftarrow \min _{v}\left\{c(x, v)+D_{v}(y)\right\}$ for each node $y \in N$

  > IF there are changes, the node will also send its own new distance vector estimate to neighbors
- under minor, natural conditions, the estimate $D_{x}(y)$ converge to the actual least cost $\mathrm{d}_{\mathrm{x}}(\mathrm{y})$


::: details Example

![](./img/04-28-10-45-24.png)

:::


**link cost changes:**
- node detects local link cost change 
- updates routing info, recalculates distance vector
- if DV changes, notify neighbors


**“good news travels fast”**

**bad news travels slow** - “count to infinity” problem!

![](./img/04-28-11-09-18.png)


An solution: **poisoned reverse**

- If Z routes through Y to get to X :
  - Z tells Y its (Z’s) distance to X is infinite (so Y won’t route to X via Z)
- will this completely solve count to infinity problem?
  > No
  >
  > ![](img/04-28-11-11-58.png)



### Comparison of LS and DV algorithms

|     |  LS     |  DV     |
| ---- |  ---  |  ---  |
| **message complexity** (how many msg to send)    |  with n nodes, E links, O(nE) msgs sent     |  exchange between neighbors only, but convergence time varies, and vulnerable to count-to-infinity      |
| **speed of convergence**    | LS: $O(n^2)$ algorithm requires O(nE) msgs, but may have **oscillations**      | convergence time varies  (*may be routing loops / count-to-infinity problem* )     |
| **robustness**: what happens if router malfunctions?    |   node can advertise incorrect link cost | DV node can advertise incorrect path cost      |
|     |  each node computes only its own table   :)  | each node’s table used by others,  error propagate thru network  :(    |



## intra-AS routing in the Internet: OSPF

> Our routing study so fat is idealized, with identical routers and a flat network
> 
> In practice, we will not store the whole forwarding vector of every host, the network will be overwhelemed by simply exchanging FVs


Solution in the Internet: **administrative autonomy**
- internet = network of networks
- each network admin may want to control routing in its own network

### Making routing scalable

aggregate routers into regions known as **“autonomous systems” (AS) (a.k.a. “domains”)**

- intra-AS routing
  - routing among hosts, routers in same AS (“network”)
  - all routers in AS must run same **intra-domain protocol**
  - routers in different AS can run different intra-domain routing protocol
  - gateway router: at “edge” of its own AS, has link(s) to router(s) in other AS’es
- inter-AS routing
  - routing among AS’es
  - **gateways** perform inter- domain routing (as well as intra-domain routing)


![](./img/04-28-11-20-54.png)

> We focus on Intra-routing in this section
> many intro-AS routing protocols availble, we only introduce OSPF



### OSPF (Open Shortest Path First)


- “open”: publicly available
- uses **link-state algorithm**
  - link state packet dissemination
  - topology map at each node
  - route computation using Dijkstra’s algorithm
- router floods OSPF link-state advertisements to all other routers in **entire** AS
  - carried in OSPF messages directly over IP (rather than TCP or UDP)
  - link state: for each attached link

### OSPF “advanced” features
- security: all OSPF messages authenticated (to prevent malicious intrusion)
- **multiple** same-cost **paths** allowed (only one path in RIP)
- integrated uni- and **multi-cast** support:
  - Multicast OSPF (MOSPF) uses same topology data base as OSPF
- **hierarchical** OSPF in large domains.
  > when the domain itself is large
  >
  > Hierarchical OSPF
  >
  >![](./img/04-28-11-28-20.png)


### Hierarchical OSPF
- **two-level hierarchy**: local area, backbone.
  - link-state advertisements only in area
  - each nodes has detailed area topology; only know direction (shortest path) to nets in other areas.
- **area border routers**: “summarize” distances to nets in own area, advertise to other Area Border routers.
- **backbone routers**: run OSPF routing limited to backbone.
- **boundary routers**: connect to other AS’es.


## Internet inter-AS routing: BGP

- **BGP (Border Gateway Protocol)**: the de facto inter-domain routing protocol
  - “glue that holds the Internet together” 
- BGP provides each AS a means to:
  - **eBGP**: obtain subnet reachability information from neighboring ASes
  - **iBGP**: propagate reachability information to all AS- nternal routers.
  - determine “good” routes to other networks based on reachability information and **policy**
  > Recall, in primitive routers, we only care about cost, but for inter-AS, policy matters a lot!
- allows subnet to advertise its existence to rest of Internet: **“I am here”**

![](./img/04-28-11-36-35.png)

### BGP Basics

- **BGP session:** two BGP routers (“peers”) exchange BGP messages *over semi-permanent TCP connection*:
  - advertising **paths** to different destination network prefixes (BGP is a “path vector” protocol)
- when AS3 gateway router 3a advertises path **AS3,X** to AS2 gateway router 2c:
  - AS3 **promises** to AS2 it will forward datagrams towards X

![](./img/04-28-11-38-11.png)

### Path attributes and BGP routes

- advertised prefix includes BGP attributes 
  - prefix + attributes = “route”
- two important attributes:
  - `AS-PATH`: list of ASes through which prefix advertisement has passed
  - `NEXT-HOP`: IP address of the router interface that begins the AS-PATH
- Policy-based routing:
  - gateway receiving route advertisement uses **import policy** to accept/decline path (e.g., never route through AS Y).
  - AS policy also determines whether to **advertise** path to other neighboring ASes
  > determined by AS's own policy
