---
sidebar_position: 5
---

# Overview

:::caution
This conceptual guide to an auction smart contract in Plutus introduces fundamentals for educational use. 
However, it is not optimized for security or efficiency and should not be deployed in production environments. 
This example simplifies some security aspects, leading to potential vulnerabilities. 
For detailed insights on developing secure smart contracts, please refer to the **[Cardano Plutus Script Vulnerability Guide](https://library.mlabs.city/common-plutus-security-vulnerabilities)** by MLabs. 
:::

## About this example

This example presents Plutus Tx code for a smart contract that controls the auction of an asset, which can be executed on the Cardano blockchain. 
In a sense, the smart contract is acting as the auctioneer in that it enforces certain rules and requirements in order for the auction to occur successfully.

<!-- talking about "what is Plutus Tx" -->

Plutus Tx is a high-level language for writing the validation logic of the contract, the logic that determines whether a transaction is allowed to spend a UTXO. 
Plutus Tx is not a new language, but rather a subset of Haskell, and it is compiled into Plutus Core, a low-level language based on higher-order polymorphic lambda calculus. 
Plutus Core is the code that runs on-chain, i.e., by every node validating the transaction, using an interpreter known as the CEK machine. 
A Plutus Core program included in a Cardano transaction is often referred to as Plutus script or Plutus validator.

<!-- talking about "the larger context of smart contract development and deployment" -->

To develop and deploy a smart contract, you would also need off-chain code for building transactions, submitting transactions, deploying smart contracts, querying for available UTXOs on the chain and so on. 
You may also want a front-end interface for your smart contract for better user experiences. 
In this example, we are not covering these aspects.

<!-- this entire next section could maybe be moved to the CORE CONCEPTS section -->
<!-- talking about "basic concepts" -->

Before we get to the Plutus Tx code, let's briefly go over some basic concepts, including UTXO, EUTXO, datum, redeemer, and script context. 

