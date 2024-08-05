---
sidebar_position: 15
---

# Plutus foundation

In order for an application to run its trusted kernel of logic as a script on a ledger, the ledger needs a way of specifying and executing scripts. 
Scripts are simply programs, so this means we need a *programming language*.

## Plutus Core

In the Plutus Platform, this language is *Plutus Core*. 
Plutus Core is designed for simplicity, determinism, and to allow careful cost control of program execution. 
Plutus Core is our "assembly language." 
Plutus Core is a low-level language based on higher-order polymorphic lambda calculus, a well-studied formalism for computing. 
Using the lambda calculus makes it an easy compilation target for functional programming languages, and allows us to have a simple, formally verified evaluator.

Plutus Core is designed to be written by a compiler, and the Platform provides a compiler from a subset of Haskell to Plutus Core. 

Plutus Core is the code that runs on-chain, i.e., by every node validating the transaction, using an interpreter known as the CEK machine. 
A Plutus Core program included in a Cardano transaction is often referred to as a Plutus script or a Plutus validator.

## Plutus Tx

Plutus Tx is a high-level language for writing the validation logic of the contract, the logic that determines whether a transaction is allowed to spend a UTXO. 
Plutus Tx is not a new language, but rather a subset of Haskell, and it is compiled into Plutus Core. 

Plutus Tx is also a Haskell library that provides a compiler for writing Plutus smart contracts in Haskell. 
Plutus Tx enables developers to write secure and reliable smart contracts which are then compiled to the Plutus Core language for execution on the Cardano blockchain. 

This allows developers to seamlessly write applications in Haskell, while compiling part of the code to on-chain Plutus Core, and part into an off-chain application.

Supporting "mixed" code in this way enables libraries written with the Plutus Haskell SDK to share logic and datatypes across both parts of the application, reducing the risk of errors significantly.

## Further reading

The formal details of Plutus Core are in its [specification](https://github.com/IntersectMBO/plutus#specifications-and-design). 

The design is discussed in the [technical report](https://plutus.cardano.intersectmbo.org/resources/plutus-report.pdf).
