---
title: Chapter 2 Application Layer
date: 2021-03-09 08:39:54
tags: 
- Computer Networks

categories: 
- Courses

sidebar: true
lang: en-US
---


<!-- more -->


## Principles of network applications

### Application Architectures

**Client-server Architecture**

- server:
  - always-on host
  - permanent IP address 
  - server *farms* for scaling
- clients:
  - communicate with server 
  - may be *intermittently connected*
  - may have *dynamic IP addresses*
  - do not communicate directly with each other

**Pure P2P architecture**

- no always-on server 
- arbitrary end systems directly communicate
- peers are intermittently connected and change IP addresses
- example: Gnutella

> Highly scalable but difficult to manage
> 
> The network formed between peers are also known as overlay network
> 
> Though conceptually, nodes are directly connected, but the connection is actually based on the infrastructures provided by the Internet

**Hybrid of client-server and P2P**

- Skype
  - Internet telephony app
  - Finding address of remote party: centralized server(s) 
  - Client-client connection is direct (not through server)
- Instant messaging
  - Chatting between two users is P2P
  - Presence detection/location centralized:
    - User registers its IP address with central server when it comes online
    - User contacts central server to find IP addresses of buddies

### Process Communicating

**Process**: program running within a host.
- Recall in OS, within same host, two processes communicate using inter-process communication.
- processes in different hosts communicate by exchanging messages
  - **Client process**: process that *initiates communication*
  - **Server process**: process that *waits to be contacted*

Note: applications with P2P architectures have **both** client processes & server processes

### Sockets

![](./img/03-09-09-28-58.png)

process sends/receives messages to/from its **socket**. Socket provides application layer with a series of **API**: 
1. **choice** of transport protocol; 
2. ability to **fix a few parameters** (lots more on this later)

> Socket seperate the process (which is controled by app developer) and the lower-level network services (which should be controled by OS)

::: tip Addressing processes

To receive messages, process must have **identifier**. The 32-bit IP address certainly can't suffice for identifying processes

identifier includes **both IP address and port numbers** associated with process on host. e.g.
- HTTP server: 80
- Mail server: 25

:::

### Message Format

App-layer protocol defines
- **Types of messages** exchanged,
  - e.g., request, response 
- Message **syntax**:
  - what fields in messages & how fields are delineated
- Message **semantics**
  - meaning of information in fields
- Rules for when and how processes send & respond to messages

Typical Application Protocol includes

- **Public-domain protocols**:
  - defined in RFCs
  - allows for interoperability 
  - e.g., HTTP, SMTP 
- **Proprietary protocols**:
  - e.g., Skype



### Requirements for Message Transport



## Web and HTTP



## FTP



## Electronic Mail (SMTP, POP3, IMAP)



## DNS