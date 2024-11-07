---
sidebar_position: 0
---

# Plutus User Guide

Welcome to the Plutus user guide.

This guide focuses primarily on Plutus Tx, a subset of Haskell tailored for implementing smart contracts on Cardano.
As a subset of Haskell, Plutus Tx is high level and purely functional, and leverages Haskell's powerful type system.
This empowers developers to write secure, reliable and deterministic code, which is essential for smart contract development.

Plutus Tx is used to write on-chain code, often called scripts or validators.
To fully develop and deploy smart contracts, off-chain code is also needed for tasks such as building and submitting transactions, querying available UTXOs, and more.
A detailed discussion of off-chain code is beyond the scope of this guide.

Besides Plutus Tx, this guide also covers other languages and components in the [plutus repository](https://github.com/IntersectMBO/plutus), including Untyped Plutus Core, Typed Plutus Core, Plutus IR, evaluation and costing of programs, among other topics.
While these subjects are not covered in depth, you can find links to specifications and papers for further reading in the [Further Resources](./delve-deeper/further-resources.md) section.
Visit the [Glossary](./glossary.md) page for brief descriptions of these concepts.
