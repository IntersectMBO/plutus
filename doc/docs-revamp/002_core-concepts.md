---
title: "Core concepts"
description: "A set of definitions of core concepts"
date: 2024-03-12
---

# Section 2. Core concepts

## Resources to inform this section: 
- Blog: [Plutus Tx: compiling Haskell into Plutus Core](https://iohk.io/en/blog/posts/2021/02/02/plutus-tx-compiling-haskell-into-plutus-core/), by Michael Peyton Jones, Feb. 2021
   - This is several years old, but the underlying essential definitions and concepts are still applicable. 
- Draft document: [Smart contracts security and best practices](https://docs.google.com/document/d/1CrWYmG-I-Z2KeB06pPM9TqvjpSgpgt8e4ipLY9vJDKE/edit?usp=sharing) being prepared by Luka Kurnjek, Education team
- [An Introduction to Plutus Core](https://blog.hachi.one/post/an-introduction-to-plutus-core/)

## Core concepts
- Names, terminology, ecosystem
- Ledger
- Scripts and the EUTXO model
- Different kinds of scripts
- Plutus Core
- Plutus Tx
- Plutus Haskell SDK
- Plutus language versions

## Understanding the Plutus platform
- What is Plutus?
	- The relationship between Plutus, Haskell, and Cardano
- Anatomy of a smart contract
- A thumbnail sketch of Plutus smart contract developer workflow
   - Most common tasks
- Plutus Components:
	- Plutus Core (The foundational layer, low-level programming language for smart contracts on Cardano.)
	- Plutus Tx (The library for writing high-level Haskell code that gets compiled down to Plutus Core)
- The Extended UTXO Model (EUTXO):
	- How it differs from the account-based model
	- Advantages for smart contracts

