---
sidebar_position: 35
---

# Glossary

### address

The address of an UTXO says where the output is "going".
The address stipulates the conditions for unlocking the output.
This can be a public key hash, or (in the Extended UTXO model) a script hash.

### Cardano

The blockchain system upon which the Plutus Platform is built.

### currency

A class of token whose minting is controlled by a particular monetary policy script.
On the Cardano ledger there is a special currency called `ada` which can never be minted and which is controlled separately.

### datum

The data field on script outputs in the Extended UTXO model.

### Extended UTXO Model

The ledger model which the Plutus Platform relies on.
This is implemented in the Alonzo hard fork of the Cardano blockchain.

>   See [Ledgers](../essential-concepts/ledger.md).

### minting

A transaction which mints tokens creates new tokens, providing that the corresponding minting policy script is satisfied.
The amount minted can be negative, in which case the tokens will be destroyed instead of created.

### minting policy script

A script which must be satisfied in order for a transaction to mint tokens of the corresponding currency.

### Hydra

A Layer 2 scalability solution for Cardano. 

For a detailed technical report, please see: 

> Manuel M. T. Chakravarty, Sandro Coretti, Matthias Fitzi, Peter Gazi, Philipp Kant, Aggelos Kiayias, and Alexander Russell. [Hydra: Fast Isomorphic State Channels. Technical Report, Cryptology ePrint Archive, Report 2020/299, 2020](https://eprint.iacr.org/2020/299). 

### distributed ledger

### ledger

>   See [Ledgers](../essential-concepts/ledger.md).

### Marlowe

A domain-specific language for writing financial contract applications. 

> See [Marlowe documentation](https://docs.marlowe.iohk.io/docs/introduction). 

### multi-asset

A generic term for a ledger which supports multiple different asset types natively.

### off-chain code

The part of a contract application’s code which runs off the chain, usually as a contract application.

### on-chain code

The part of a contract application’s code which runs on the chain (i.e. as scripts).

### Plutus Core

Plutus Core is our "assembly language." 
It is a low-level language based on higher-order polymorphic lambda calculus, a well-studied formalism for computing. 
Using the lambda calculus makes it an easy compilation target for functional programming languages, and allows us to have a simple, formally verified evaluator.

Plutus Core is the code that runs on-chain, i.e., by every node validating the transaction, using an interpreter known as the CEK machine. 
A Plutus Core program included in a Cardano transaction is often referred to as Plutus script or Plutus validator.

Plutus Core is designed for simplicity, determinism, and to allow careful cost control of program execution. 

### Plutus IR

An intermediate language that compiles to Plutus Core.
Plutus IR is not used by users, but rather as a compilation target on the way to Plutus Core.
However, it is significantly more human-readable than Plutus Core, so should be preferred in cases where humans may want to inspect the program.

### Plutus Platform

The combined software support for writing contract applications, including:

   1. Plutus foundation, and

   2. Plutus application framework

   Please see: 
   
   - [Plutus platform](../essential-concepts/plutus-platform.mdx)
   - [Plutus foundation](../essential-concepts/plutus-foundation.md)

### Plutus Tx

Plutus Tx is a high-level language for writing the validation logic of a smart contract, the logic that determines whether a transaction is allowed to spend a UTXO. Plutus Tx is not a new language, but rather a subset of Haskell, and it is compiled into Plutus Core, a low-level language based on higher-order polymorphic lambda calculus. Plutus Core is the code that runs on-chain, i.e., by every node validating the transaction, using an interpreter known as the CEK machine. 

Plutus Tx is also the libraries and compiler for compiling Haskell into Plutus Core to form the on-chain part of a contract application.

### redeemer

The argument to the validator script which is provided by the transaction which spends a script output.

### rollback

The result of the local node switching to the consensus chain.

### script

A generic term for an executable program used in the ledger.
In the Cardano blockchain, these are written in Plutus Core.

### script context

A data structure containing a summary of the transaction being validated, as well as a way of identifying the current script being run.

### script output

A UTXO locked by a script.

### token

A generic term for a native tradeable asset in the ledger.

### transaction output

Outputs produced by transactions.
They are consumed when they are spent by another transaction.
Typically, some kind of evidence is required to be able to spend a UTXO, such as a signature from a public key, or (in the Extended UTXO Model) satisfying a script.

### UTXO

An unspent [transaction output](glossary.md#transaction-output).

### utxo congestion

The effect of multiple transactions attempting to spend the same [transaction output](glossary.md#transaction-output).

### validator script

The script attached to a script output in the Extended UTXO model.
Must be run and return positively in order for the output to be spent.
Determines the address of the output.
