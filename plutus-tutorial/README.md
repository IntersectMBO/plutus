# PlutusTx Tutorial

This project contains a collection of tutorials that explain various aspects of the PlutusTx smart contract platform.

1. [Introduction to Plutus](./tutorial/Intro.md) introduces smart contracts and related terms
2. [Plutus Tx](./doctest/Tutorial/01-plutus-tx.md) explaining the basics of using the Plutus Tx compiler to create embedded (on-chain) programs
3. [Wallet API, Part I](./doctest/Tutorial/02-validator-scripts.md) implements a guessing game. Topics covered:
  * Signature of validator script
  * `Ledger.makeLift`, `Ledger.compileScript`
  * Contract endpoints
  * `Wallet.payToScript_`, `Wallet.collectFromScript`
  * Playground
4. [Wallet API, Part II](./doctest/Tutorial/03-wallet-api.md) implements a crowdfunding campaign. Topics covered:
  * Parameterising a contract through partial application using `Ledger.applyScript`
  * Operators in on-chain code
  * On-chain time (slot intervals)
  * Working with Ada values
  * Blockchain triggers
5. Mockchain (emulator), [Part 1](./tutorial/Tutorial/TH.hs) and [Part 2](./tutorial/Tutorial/Emulator.hs) deal with developing contracts off-line, as Haskell modules. Topics covered:
  * Developing contracts in GHCi
  * How does the mockchain work
  * Writing and running traces from the terminal
6. [A multi-stage contract](./tutorial/Tutorial/Vesting.hs) implements a vesting scheme. Topics covered:
  * Writing a contract that extends over multiple transactions

Note that (4) and (5) are written as regular Haskell modules and include exercises (marked by `error`). They are intended to be edited interactively with the help of GHCi. See [4.1](./tutorial/Tutorial/TH.hs) for details.
Solutions for the exercises are located in `Solutions1.hs`.

Additional documentation will be added for the following work-in-progress features, when they are available on the mockchain:

* Forging new currencies
* Using NFTs to represent permissions
* Decoding values from their on-chain representation back to Haskell

# Prerequisites

To follow the [Wallet API, Part I](./tutorial/Tutorial/02-validator-scripts.md) and [Wallet API, Part II](./tutorial/Tutorial/03-wallet-api.md) tutorials you should have access to a recent version of the Plutus Playground.

To follow the mockchain tutorial, [Part 1](./tutorial/Tutorial/TH.hs) and [Part 2](./tutorial/Tutorial/Emulator.hs), you should have a local copy of the source code, and a recent GHC and cabal in your environment. See below for instructions on setting this up on Windows and Ubunutu systems.

The [multi-stage contract](./tutorial/Tutorial/Vesting.hs) code works in the Playground and in GHCi alike.

# Installing the emulator locally

## Windows

To install the emulator (not the Playground) locally, follow these steps on Windows 10.

1. Clone this repository
2. Install the "Ubuntu 18.04" app from the app store
3. Open the "Ubuntu 18.04" terminal by clicking on the icon
4. Install the nix package manager following the instructions on https://nixos.org/nix/
5. *IMPORTANT* Add the IOHK binary cache to your Nix configuration. See [here](../README.md) for details, section "Binary caches"
6. cd to the plutus-tutorial folder
7. type `nix-shell`. This will download all of the dependencies and populate the PATH with a correctly configured cabal. If `nix-shell` results in nix attempting to compile a lot of dependencies then something went wrong earlier and you should go back to step 4.
8. type `cabal repl plutus-tutorial`

## Ubuntu

Follow steps 4-8 above.
