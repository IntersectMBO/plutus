# Introduction to Plutus

Plutus is the smart contract platform of the Cardano blockchain. Plutus contracts consist of pieces that go on the blockchain (on-chain code) and pieces that run on the user's machine (off-chain or client code). 

Both on-chain and off-chain code is written in Haskell, and Plutus smart contracts are Haskell programs. Off-chain code is compiled by GHC, the Haskell compiler, and on-chain code is compiled by the Plutus compiler. 

## Smart contracts

From the smart contract author's perspective, the blockchain is a distributed bookkeeping system. It keeps track of who owns how much of a virtual resource (Bitcoin, Ada, etc.) and records when assets are transferred from one entity to another. The owners of digital assets are identified by their public keys, and they may be people or machines.

Smart contracts are programs that control the transfer of resources on the blockchain. When two parties decide to enter a smart contract, they place some of their own assets under the control of the contract. Every time somenone wants to take assets out of the contract, the program is run and only if its output is positive are the assets released. 

In the [next tutorial](../doctest/Tutorial/02-validator-scripts.md) we will write our first smart contract, a guessing game.

## Glossary

- Extended UTxO
    - The ledger model on which the Plutus Platform is based.
- On-chain code
    - Code written as part of a smart contract which executes on the chain during
      transaction validation.
- Off-chain code
    - Code written as part of a smart contract which executes off the chain, usually
      in a user's wallet.
- Plutus Core
    - A small functional programming language designed to run as on-chain code.
- Plutus IR
    - An intermediate language that compiles to Plutus Core, for use as a target
      language for compiler writers.
- Plutus Platform
    - The combined software support for writing smart contracts, including:
        - Libraries for writing off-chain code in Haskell.
        - Libraries for writing on-chain code in Plutus Tx.
        - Emulator support for testing smart contracts.
- Plutus Tx
    - A subset of Haskell which is compiled into Plutus Core.
