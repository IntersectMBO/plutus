---
sidebar_position: 2
---

# Getting started with Plutus Tx

## Plutus-Tx-Template repository

The easiest way to create a Cardano smart contract is to start with the template provided in the [Plutus-Tx-template repository](https://github.com/IntersectMBO/plutus-tx-template). Follow the instructions in the README file to setup your environment and run the example project. 

### Overview of creating a validator script using the template repo

1. Clone the Plutus-Tx template repo.
2. Install Nix. See the [Nix setup guide](https://github.com/input-output-hk/iogx/blob/main/doc/nix-setup-guide.md) for installing and configuring nix to work with projects at IOG. Add the IOG binary cache to your nix configuration to speed up builds. 
3. From the repo, run `nix develop` (select `y` for all question prompts).
4. Run `cabal update`.
5. Using `cardano-cli`, generate a pubKeyHash.
6. Set posix time and pubKeyHash in `Main.hs`.
7. Run `cabal build plutus-tx-template`.
8. Run `cabal exec plutus-tx-template`.

#### Expected result
The expected result is that the above process will have created the `validator.uplc` script.

#### Deploying and interacting with your script

Use `cardano-cli` to deploy your script. 

Use an off-chain framework, such as [cardano-transaction-lib](https://github.com/Plutonomicon/cardano-transaction-lib) and [lucid](https://github.com/spacebudz/lucid), to interact with your script. 

All these are based on the [Cardano API](https://github.com/IntersectMBO/cardano-node/tree/master/cardano-api), a low-level API that provides the capability to do the off-chain work with a local running node.
