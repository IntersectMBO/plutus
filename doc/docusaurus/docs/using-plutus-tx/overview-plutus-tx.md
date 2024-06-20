---
sidebar_position: 5
---

# High-level overview of how Plutus Tx works

Plutus Tx is a high-level language for writing the validation logic of the contract, the logic that determines whether a transaction is allowed to spend a UTXO. 
Plutus Tx is not a new language, but rather a subset of Haskell, and it is compiled into Plutus Core, a low-level language based on higher-order polymorphic lambda calculus. 
Plutus Core is the code that runs on-chain, i.e., by every node validating the transaction, using an interpreter known as the CEK machine. 
A Plutus Core program included in a Cardano transaction is often referred to as a Plutus script or a Plutus validator.

To develop and deploy a smart contract, you also need off-chain code for building transactions, submitting transactions, deploying smart contracts, querying for available UTXOs on the chain, and so on. 
You may also want a front-end interface for your smart contract for better user experiences. 

A Plutus application, or `Plutus Tx` program, where 'Tx' indicates that the component usually goes into a transaction, is written as a single Haskell program. 
The Plutus Tx program describes both the code that runs off the chain (for example, on a user's computer, or in their wallet), and on the chain as part of transaction validation.
The parts of the program that describe the on-chain code are compiled into `Plutus Core`. 

## Staged metaprogramming

The key technique used to implement Plutus Tx is called *staged metaprogramming*, which means that the main Haskell program generates *another* program (in this case, the Plutus Core program that will run on the blockchain). 
Plutus Tx is the mechanism used to write those programs, but since Plutus Tx is just part of the main Haskell program, we can share types and definitions between the two.

