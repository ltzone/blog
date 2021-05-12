---
title: Chapter 6 - Link Layer
date: 2021-05-12 11:19:58
tags: 
- Computer Networks

categories: 
- Courses

sidebar: true
lang: en-US
---

*our goals:*

- understand principles behind link layer services:
  - error detection, correction

    > Recall in TCP, error detection for segment, retransmission on failure
    >
    > For link layer, just correct it! (flip the bit)

  - sharing a broadcast channel: multiple access 

  - link layer addressing

  - local area networks: Ethernet, VL ANs

- instantiation, implementation of various link layer technologies

<!-- more -->

## Introduction

### Terminologies

- any device that runs a link-layer protocol (hosts, routers, switches, wifi access points) : **nodes**
- communication channels that connect adjacent nodes along communication path: **links**
  - wired links
  - wireless links 
  - LANs
- layer-2 packet: **frame**, encapsulates datagram

***data-link layer*** has responsibility of transferring datagram from one node to ***physically adjacent*** node over a link



### Context

- datagram transferred by different link protocols over different links:
  - e.g., Ethernet on first link, frame relay on intermediate links, 802.11 on last link

- each link protocol provides different services 
  - e.g., may or may not provide rdt over link



### Services

> Link layer will not only add headers, but also trailors!

- framing, link access:
	- encapsulate datagram into frame, adding header, trailer
	- channel access if shared medium
	- “MAC” addresses used in frame headers to identify source, destination
	  - different from IP address!

- *reliable delivery between adjacent nodes*

  - we learned how to do this already (chapter 3)!

  - **seldom used** on low bit-error link (fiber, some twisted pair)

  - wireless links: high error rates

     - *Q:* why both **link-level**(for every link) and **end-end reliability**?

       > pure end-end will bring about great overhead

- *error detection*:
  - errors caused by signal attenuation, noise.
  - receiver detects presence of errors:
    - signals sender for retransmission or drops frame
- *error correction:*
  - receiver identifies *and corrects* bit error(s) without resorting to retransmission

### Implementation

- in each and every host

- link layer implemented in “adaptor” (aka *network interface card* NIC) or on a chip
  - Ethernet card, 802.11 card; Ethernet chipset
  - implements link, physical layer

- attaches into host’s system buses
- combination of hardware, software



<img src="./img/8_link/image-20210512113954627.png" alt="image-20210512113954627" style="zoom:50%;" />

