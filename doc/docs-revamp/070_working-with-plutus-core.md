---
title: "Working with Plutus Core"
description: "Draft outline for review and comments"
date: 2024-04-04
---

# Section 7. Working with Plutus Core

## Introduction to Plutus Core

Plutus Core is the low-level language that runs on the Cardano blockchain. 
It is the language that the Cardano blockchain's ledger understands and executes.

Plutus Core is designed for simplicity, determinism, and to allow careful cost control of program execution. 
Using the lambda calculus makes it an easy compilation target for functional programming languages, and allows us to have a simple, formally verified evaluator.

Plutus Core is: 
- a minimal, typed, and functional programming language 
- the programming language in which scripts on the Cardano blockchain are written 
- not read or written by humans 
- a variant of the lambda calculus, a well-studied formalism for computing
- a compilation target for higher-level languages, such as Plutus Tx, [Aiken](https://aiken-lang.org/), [OpShin](https://github.com/OpShin/opshin) and others 

## Plutus Core Syntax and Semantics
- The basic constructs of Plutus Core, such as variables, functions, and applications, as well as the type system that includes types and kinds
- Syntax and semantics of Plutus Core
- Understanding data types used in Plutus Core and how they relate to the types in Haskell

## Compilation Process
- Understanding how high-level Plutus Tx code is compiled down to Plutus Core, including the role of the Plutus compiler and the abstract syntax tree (AST)
- Understanding the compilation target and execution environment of your Plutus Tx code

## Execution Model
- Understanding how your contracts will execute on-chain
- The low-level execution model of Plutus Core 
- The cost model for computing resource usage

## Built-in Functions
- Exploring the built-in functions and types provided by Plutus Core that are essential for contract execution.

## Formal Specification of Plutus Core
- The formal [Plutus Core Specification](https://ci.iog.io/job/input-output-hk-plutus/master/x86_64-linux.packages.plutus-core-spec/latest/download/1) for understanding the precise behavior of the Plutus Core language.

## Security Considerations
- The security aspects of smart contract development, including auditing Plutus Core code for safety and correctness.

## Interacting with the Extended UTXO Model (EUTXO)
- Understanding how Plutus Core interacts with the ledger and the EUTXO model specific to Cardano.

## Advanced Topics
- Optimizations, bytecode generation, and other advanced features of Plutus Core for those who want to understand the language at a deeper level.

## Tools and Resources
- The tools available for Plutus Core development, such as decompilers, pretty-printers, and debuggers.
- Troubleshooting
