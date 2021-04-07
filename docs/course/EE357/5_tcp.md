---
title: Chapter 3 Transport Layer - Part II
date: 2021-04-06 09:30:09
tags: 
- Computer Networks

categories: 
- Courses

sidebar: true
lang: en-US
---


<!-- more -->


## Connection-oriented transport: TCP

- **point-to-point:**
  - one sender, one receiver
- **reliable, in-order byte steam:**
  - no “message boundaries”
- **pipelined:**
  - TCP congestion and flow control set window size
- **full duplex data:** 全双工服务
  - bi-directional data flow in same connection
  - MSS: maximum segment size
  > Exists a upper bound of segment data size
- connection-oriented:
  - handshaking (exchange of control msgs) inits sender, receiver state before data exchange
- flow controlled: 
  - sender will not overwhelm receiver

### segment structure

![](./img/04-07-10-09-42.png)

**sequence numbers:**
- byte stream “number” of the first byte in the segment’s data
- counts by bytes of data

> ![](./img/04-07-10-08-54.png)
> 
> Assume 2000 Bytes Data, and a TCP can transfer 1000 Bytes, the sequence number of the first segment is 0, for the second segment is 1000

**acknowledgements**
- seq # of next byte expected from other side
- cumulative ACK
> For the example above, the ack for the first segment should be 1000

> Example
> 
> ![](./img/04-07-10-16-20.png)

### round trip time, timeout

**Intuition**. How to set TCP timeout value?
- should be longer than RTT
  - but RTT varies
- too short $\Rightarrow$ premature timeout, unnecessary retransmissions
- too long $\Rightarrow$ slow reaction to segment loss

**Solution**.  How to estimate RTT?
- `SampleRTT`: measured time from segment transmission until ACK receipt
  - ignore retransmissions
  > Why ignore?
- `SampleRTT` will vary, want estimated RTT “smoother”
  - average several recent measurements, not just current `SampleRTT`

$$
\mathsf{EstimatedRTT} = (1-\alpha)\times \mathsf{EstimatedRTT} + \alpha \times \mathsf{SampleRTT}
$$

- exponential weighted moving average
- influence of past sample decreases exponentially fast
- typical value: a = 0.125

> `Timeout` based on `EstimatedRTT` ?

- timeout interval: `EstimatedRTT` plus **“safety margin”**
  - large variation in EstimatedRTT -> larger safety margin 
- estimate SampleRTT deviation from EstimatedRTT:
$$
\mathsf{DevRTT} = (1-b)\times \mathsf{DevRTT} + b\times|\mathsf{SampleRTT}-\mathsf{EstimatedRTT}|
$$
(typically, $b = 0.25$)

$$
\mathsf{TimeoutInterval} = \mathsf{EstimatedRTT} + 4*\mathsf{DevRTT}
$$



### reliable data transfer

First we consider a simplified TCP sender:
- ignore duplicate acks 
- ignore flow control, congestion control

::: theorem


Sender events:

- data rcvd from app:
  - create segment with seq #
  - seq # is byte-stream number of first data byte in segment
  - start timer if not already running
    - think of timer as for oldest unacked segment
    - expiration interval: TimeOutInterval
- timeout:
  - retransmit segment that caused timeout
  - restart timer 
- ack rcvd:
  - if ack acknowledges previously unacked segments
  - update what is known to be ACKed
  - start timer if there are still unacked segments

![](./img/04-07-10-37-06.png)


Scenerio, A is sender, B is receiver

|  Lost ACK   |  Premature Timeout     |       |
|  ---  |  ---  |  ---  |
|  ![](./img/04-07-10-40-07.png)     | ![](./img/04-07-10-40-14.png)      |  ![](./img/04-07-10-40-20.png)     |
| Retransmission works fine for single transmission | If the timeout is set to be small, ACK takes longer to return. B will still return ACK 120 for the re-transmission because 100 has been received. | An interesting case, even if ACK=100 is lost, but A still knows B receives by ACK=120! no transmission is required. |

> In TCP, ACK is acumulative!

**Receiver**. **not ACK immediately**, pending strategy as follows!

|  event at receiver     |  TCP receiver action     |
|  ---  |  ---  |
|  arrival of in-order segment with expected seq #. All data up to expected seq # already ACKed     |  delayed ACK. Wait up to 500ms for next segment. If no next segment, send ACK     |
|  arrival of in-order segment with expected seq #. One other segment has ACK pending     |  immediately send single cumulative ACK, ACKing both in-order segments     |
|  arrival of out-of-order segment higher-than-expect seq #. Gap detected     |  immediately send **duplicate ACK**(i.e. send the previously sent ACK again!), indicating seq. # of next expected byte     |
|  arrival of segment that partially or completely fills gap     |  immediate send ACK, provided that segment starts at lower end of gap     |

:::

> How will the duplicate ACK tell the sender to retransmit the segment (Note, in simplified model, only timeout event will trigger retransimission)

::: theorem

**TCP fast retransmit**

**Problem**.
- time-out period often relatively long:
  - long delay before resending lost packet
- detect lost segments via duplicate ACKs.
  - sender often sends many segments back- to-back
  - if segment is lost, there will likely be many duplicate ACKs.

**Solution.**

if sender receives 3 ACKs for same data (“**triple duplicate ACKs**”), (“triple duplicate ACKs”), resend unacked segment with smallest seq #
- likely that unacked segment lost, so don’t wait for timeout
 
![](./img/04-07-11-10-31.png)


:::

::: tip

TCP looks like a mixture of GBN and SR. "selective acknowledge"
- GBN, sender retransmit all > n, but TCP only retransmit at most 1 segment
- SR, separate ACK(n), TCP, acumulative ACK, sender only needs to maintain a base and next seqnum

:::


### flow control

> **Motivation**.
> 
> ![](./img/04-07-11-16-31.png)

- receiver “advertises” free buffer space by including `rwnd` value in TCP header of receiver-to-sender segments
  - RcvBuffer size set via socket options (typical default is 4096 bytes)
  - many operating systems autoadjust `RcvBuffer`
- sender limits amount of unacked (“in-flight”) data to receiver’s `rwnd` value
- guarantees receive buffer will not overflow

![](img/04-07-11-20-15.png)

::: tip

**payload**: all the data except TCP header (don't need to be buffered) in the segment

:::



### Connection Management

> Many attacks are based on SYN packet, so it is necessary to init `x` as a random number


#### build connection

TCP 3-way handshake
![](./img/04-07-11-30-11.png)

#### closing a connection

![](./img/04-07-11-37-23.png)

> Why timed wait ?
> ![](./img/04-07-11-40-50.png)