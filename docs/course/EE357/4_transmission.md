---
title: Chapter 3 Transport Layer - Part 1
date: 2021-03-24 10:18:16
tags: 
- Computer Networks

categories: 
- Courses

sidebar: true
lang: en-US
---


- understand principles behind transport layer services:
  - multiplexing/demultiplexing 多路复用
  - reliable data transfer
  - flow control in TCP
  - congestion control in TCP
- learn about transport layer protocols in the Internet:
  - UDP: connectionless transport 
  - TCP: connection-oriented transport
  - TCP congestion control


<!-- more -->


## 1 Transport-layer services

### Transport vs. application layer

- provide **logical communication** between **app processes** running on different hosts
  > From the application layer's view, it's like talking directly to another address:port in the network
- transport protocols run in end systems 
  - sender: breaks app messages into **segments**, passes to network layer 
  - receiver: reassembles segments into messages, passes to app layer
- more than one transport protocol available to apps
  - Internet: TCP and UDP

### Transport vs. network layer

- network layer: **logical** communication between **hosts**
- transport layer: **logical** communication between **processes**
  -  relies on, enhances, network layer services

### Internet transport-layer protocols


- reliable, in-order delivery (TCP)
  - congestion control 
  - flow control
  - connection setup
- unreliable, unordered delivery: UDP
  - no-frills extension of “best-effort” IP
  > - a simple augmentation of port number based on IP protocol,
  > - also make error-check extension, but no retry strategy
- services not available: 
- delay guarantees
- bandwidth guarantees



## 2 Multiplexing and demultiplexing

**Demultiplexing** at **rcv host**:
- delivering received segments to correct socket

**Multiplexing** at **send host**:
- gathering data from multiple sockets, enveloping data with header (later used for demultiplexing)

> Note, the (de)multiplexing strategy differ w.r.t. the protocol.

**host uses IP addresses & port numbers to direct segment to appropriate socket**

![](./img/03-24-11-01-28.png)

> Two segments coming from **different IP**, but have same **port numbers** will be directed into the **same** UDP socket


### Connectionless Demultiplexing

UDP sockets are identified by two-tuple `(dest IP address, dest port number)`
```
DatagramSocket mySocket1 = new DatagramSocket(99111);
DatagramSocket mySocket2 = new DatagramSocket(99222);
```

![](./img/03-24-11-01-16.png)
> SP = sender port number, DP = destination port number


### Connection-oriented demux

- TCP socket identified by 4-tuple:
  - `source IP address `
  - `source port number `
  - `dest IP address`
  - `dest port number`

- recv host uses all four values to direct segment to appropriate socket
- Server host may support many simultaneous TCP sockets:
  - each socket identified by its own 4-tuple
  - e.g. Web **servers** have different sockets for each connecting client
  - e.g. for each **client**, non-persistent HTTP will have different socket for each request

> Unlike UDP, **several sockets** will be established **on one port**
> - Now `(host address, host pair)` tuple is not enough!

![](./img/03-24-11-14-38.png)

![](./img/03-24-11-15-31.png)


## 3 Connectionless transport: UDP

User Datagram Protocol

::: theorem Why is there a UDP

- no connection establishment (which can add delay)
- simple: no connection state at sender, receiver
- small segment header
- no congestion control: UDP can blast away as fast as desired

> DNS is using UDP

:::


- “no frills,” “bare bones” Internet transport protocol
- “best effort” service, UDP segments may be:
  - lost
  - delivered out of order to app
- connectionless:
  - no handshaking between UDP sender, receiver
  - each UDP segment handled independently of others
- often used for streaming multimedia apps
  - loss tolerant 
  - rate sensitive

![](./img/03-24-11-25-02.png)

### UDP Checksum (校验和)

**Goal**. detect “errors” (e.g., flipped bits) in transmitted segment

**Sender**:
- treat segment contents as sequence of 16-bit integers
- checksum: addition (1’s complement sum) of segment contents
  > - for overflow, add the overflowed bit into the first bit
  > - takes complement
- sender puts checksum value into UDP checksum field
  
**Receiver**:
- compute checksum of received segment
  > - sum together, then sum checksum
  > - if all one, no error detected
- check if computed checksum equals checksum field value:
  - NO - error detected
  - YES - no error detected. *But maybe errors nonetheless?* More later ....

> Why sometimes can't detect, and why ensures a fair performance?

## 4 Principles of reliable data transfer