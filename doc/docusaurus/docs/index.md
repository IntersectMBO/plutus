---
sidebar_position: 0
---

# Plutus user guide

## Introduction

Plutus is the native smart contract language for the Cardano ecosystem. 

The Plutus project consists of: 
- Plutus Core, the programming language used for scripts on Cardano; 
- Tooling and compilers for compiling various intermediate languages into Plutus Core; and 
- Plutus Tx, the compiler that compiles the Haskell source code into Plutus Core to form the on-chain part of a contract application. 

All of these elements are used in combination to write Plutus Core scripts that run on the Cardano blockchain.

To develop and deploy a smart contract, you also need off-chain code for building transactions, submitting transactions, deploying smart contracts, querying for available UTXOs on the chain, and so on. You may also want a front-end interface for your smart contract for a better user experience. 

Plutus allows all programming to be done from a [single Haskell library](https://intersectmbo.github.io/plutus/master/). This lets developers build secure applications, forge new assets, and create smart contracts in a predictable, deterministic environment with the highest level of assurance. Furthemore, developers don’t have to run a full Cardano node to test their work. 

With Plutus you can:

- Forge new tokens in a lightweight environment,
- Build smart contracts, and
- Support basic multi-sig scripts.

## Getting started with Plutus Tx
See [Getting started with Plutus Tx](getting-started-plutus-tx.md) if you want to jump right in and start a project. 

## Intended audience

The intended audience of this documentation includes developers who want to implement smart contracts on the Cardano blockchain. 
This involves using Plutus Tx to write scripts, requiring some knowledge of the Haskell programming language.

This guide is also meant for certification companies, certification auditors, and people who need an accurate specification. 
See, for example:

- the [Cardano ledger specification](https://github.com/IntersectMBO/cardano-ledger#cardano-ledger)
- the [Plutus Core specification](https://github.com/IntersectMBO/plutus#specifications-and-design)
- the [public Plutus code libraries](https://intersectmbo.github.io/plutus/master/) generated using Haddock. 

## The Plutus repository

The [Plutus repository](https://github.com/IntersectMBO/plutus) includes: 

* the implementation, specification, and mechanized metatheory of Plutus Core 
* the Plutus Tx compiler 
* the combined documentation, generated using Haddock, for all the [public Plutus code libraries](https://intersectmbo.github.io/plutus/master/), such as `PlutusTx.List`, enabling developers to write Haskell code that can be compiled to Plutus Core.

## Educational resources

The IOG Education Team provides the IOG Academy Haskell Course and the Plutus Pioneer Program (PPP) to attract and train software developers in Plutus. 

If you are new to Plutus or are looking for additional educational material, please see the following resources: 

- [IOG Academy Haskell Course](https://www.youtube.com/playlist?list=PLNEK_Ejlx3x1D9Vq5kqeC3ZDEP7in4dqb)
- [Plutus Pioneer Program Gitbook](https://iog-academy.gitbook.io/plutus-pioneers-program-fourth-cohort/)
- [Plutus Pioneer Program GitHub page](https://github.com/input-output-hk/plutus-pioneer-program)
- IOG's technical community on Discord for PPP. Follow this [invitation link](https://iohk.us20.list-manage.com/track/click?u=26d3b656ecc43aa6f3063eaed&id=46c99986ab&e=6489217014) to join the discord server.
