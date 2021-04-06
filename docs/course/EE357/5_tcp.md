---
title: Transport Layer (II)
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



### segment structure

**sequence numbers:**
- byte stream “number” of the first byte in the segment’s data
- counts by bytes of data
> Assume 2000 Bytes Data, and a TCP can transfer 1000 Bytes, the sequence number of the first segment is 0, for the second segment is 1000

**acknowledgements**
- seq # of next byte expected from other side
- cumulative ACK
> For the example above, the ack for the first segment should be 1000

**MSS** maximal segment length






### reliable data transfer



### flow control



### connection management