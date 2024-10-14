---
sidebar_position: 25
---

# Glossary

### Address

Each UTXO has an address, which stipulates the conditions for spending the UTXO.

An address on Cardano can be based on either a public key hash, which requires a private key signature corresponding to the public key hash to spend the UTXO, or a script hash, which requires the script with that particular hash to be executed to spend the UTXO.
These are referred to as public key address and script address, respectively.

### Cardano

The blockchain system for which Plutus Core and Plutus Tx are built.

### Contract Blueprint

A contract blueprint enables communication between on-chain code and off-chain code written in different languages.
It is introduced in [CIP-57](https://developers.cardano.org/docs/governance/cardano-improvement-proposals/cip-0057/).
Also see [Producing a Plutus Contract Blueprint](./working-with-scripts/producing-a-blueprint.md).

### Currency Symbol and Token Name

On Cardano, each class of tokens (or asset class) is identified by its currency symbol (also known as currency, or asset group) along with the token name.
The minting and burning of a token are controlled by the Plutus script whose hash corresponds to the token's currency symbol.

Ada/Lovelace is a special asset class where the currency symbol and token name are both empty strings, and it cannot be minted or burned via transactions.

See [_UTXOma: UTXO with Multi-Asset Support_](https://iohk.io/en/research/library/papers/utxomautxo-with-multi-asset-support/).

### Datum

A piece of data attached to a UTXO at a script address.
The datum serves as an input to the script, and is often used to represent the state of a smart contract.

### Extended UTXO Model (EUTXO)

An extended version of the UTXO model, where each UTXO can carry additional data (or "datum"), and be associated with a Plutus script that specifies the conditions under which the UTXO can be spent.
See [_The Extended UTXO Model_](https://iohk.io/en/research/library/papers/the-extended-utxo-model/).

### Guardrail Script

A guardrail script, sometimes referred to as a constitution script or a proposing script, is a Plutus V3 script used to validate two kinds of governance actions: parameter change and treasury withdrawal.
See [Script Purposes](./working-with-scripts/script-purposes.md).

### Inline Datum

Inline datums are a feature introduced in the Babbage era.
Before babbage, a UTXO could only contain a datum hash, not the datum itself.
To spend such a UTXO, the corresponding datum must be provided in the transaction.
Inline datums allow datums to be directly attached to UTXOs.

For more details, see [CIP-32](https://cips.cardano.org/cip/CIP-32).

### Hard Fork

A hard fork is an update of the major protocol version, i.e., transitioning the protocol version from `x.y` to `x+1.0`.
A hard fork is required when a backwards incompatible change to the Cardano node is made, causing the old node to reject some blocks produced by the new node.
As a result, old nodes are no longer able to validate the chain, and all participants must upgrade to the new version.
A hard fork is initiated by a transaction that updates the protocol version.
The protocoal version is one of the protocol parameters, and like other protocol parameter changes, a hard fork always takes effect at an epoch boundary.

A hard fork may or may not introduce a new ledger era.
The latter is called an intra-era hard fork.
For example, the Vasil hard fork introduced the Babbage era, and the Chang hard fork introduced the Conway era.
The Valentine hard fork is an example of an intra-era hard fork.

### Ledger Era

A ledger era marks a specific period where new features are added to the Cardano ledger, for instance

- The Alonzo era, which followed the Alonzo hard fork, introduced smart contracts and Plutus V1.
- The Babbage era, which followed the Vasil hard fork, introduced Plutus V2 along with features such as reference scripts and inline datum.
- The Conway era, which followed the Chang hard fork, introduced Plutus V3 and features such as governance actions and voting.

A hard fork is required to introduce a new ledger era, but a hard fork does not necessarily introduce a new ledger era.

### Ledger Language Version

This is what "Plutus V1", "Plutus V2", "Plutus V3" refer to.
See [Different Notions of Version](./essential-concepts/versions) and [Plutus Ledger Language Version](./working-with-scripts/ledger-language-version).

### Minting Policy Script

A Plutus script which must be satisfied in order for a transaction to mint tokens of the corresponding currency.

### Off-chain Code

Code executed by individual applications rather than Cardano nodes.
This includes functions like building, signing, and submitting transactions.
Off-chain code can be developed using libraries like [Mesh](https://meshjs.dev/), [PyCardano](https://pycardano.readthedocs.io/en/latest/) and [Cardano API](https://github.com/IntersectMBO/cardano-api).

### On-chain Code

Code executed directly on the Cardano blockchain by each participating node.
The main function of on-chain code is for nodes to validate transactions, such as checking if a transaction is permitted to spend a UTXO or mint a token.
On-chain code is usually written in a high level language like Plutus Tx, and compiled into Untyped Plutus Core (UPLC).
The Cardano node includes an evaluator that runs UPLC programs.

### The Plugin

The compiler from Plutus Tx to Untyped Plutus Core, which is implemented as a GHC plugin.

### Plutus

The term "Plutus" can refer to Untyped Plutus Core, Typed Plutus Core, or, prior to its renaming to Plinth, Plutus Tx.
To avoid ambiguity, it is advisable not to use "Plutus" on its own.

### Plutus Core

The term "Plutus Core" can refer either to Untyped Plutus Core or Typed Plutus Core, depending on the context.
To avoid confusion, it is recommended to use UPLC for Untyped Plutus Core and TPLC for Typed Plutus Core.

### Plutus IR

An intermediate language that compiles to Plutus Core.
See [Plutus Core and Plutus Tx](./essential-concepts/plutus-core-and-plutus-tx.md).

### Plutus Metatheory

The formalization of typed and untyped Plutus Core.
In the future we may add Plutus IR to the formalization.
It is "meta" in the sense that it is a framework for reasoning about the Plutus Core languages themselves.

### Plutus Script/Validator

A Plutus script, or Plutus validator, is a UPLC program executed on-chain.
Sometimes a program written in a high level language that compiles to UPLC, such as Plutus Tx, is also referred to as a Plutus script.

### Plutus Tx

Plutus Tx is a high-level language for writing the validation logic of transactions. See [Plutus Core and Plutus Tx](./essential-concepts/plutus-core-and-plutus-tx.md).

### Protocol Parameters

Various settings that control the behavior of the Cardano blockchain.

### Protocol Version

A key protocol parameter that indicates the current version of the blockchain protocol in use.
It is in the form of `x.y`, where `x` is the major protocol version and `y` is the minor protocol version.
A hard fork bumps the major protocol version, while a soft fork bumps the minor protocol version.

Protocol versions are closely tied to Cardano node versions.
A node of major version `x` supports up to major protocol version `x`.
Thus after a hard fork that bumps the major protocol version to `x+1`, node version `x` or older will become obsolete, requiring all participants to upgrade their nodes.

### Redeemer

A piece of data included in a transaction that serves as an input to a Plutus script that needs to be executed to validate this transaction.

If a smart contract is regarded as a state machine, the redeemer would be the input that ticks the state machine.

### Reference Input

Reference inputs are a feature introduced in the Babbage era.
A reference input is a UTXO that a transaction can inspect without having to consume it.
Recall that a UTXO can only be consumed once.
Since a UTXO can only be consumed once, reference inputs help avoid the need to keep consuming and recreating similar UTXOs.

For more details, see [CIP-31](https://cips.cardano.org/cip/CIP-31).

### Reference Script

Reference scripts are a feature introduced in the Babbage era.
Before Babbage, a UTXO could not contain scripts, so spending a UTXO with a script address required the script to be included in the transaction.
Reference scripts allow scripts to be attached to UTXOs, which can then be used as reference inputs.
This reduces transaction sizes, and avoids the need to include the same scripts in multiple transactions.

For more details, see [CIP-33](https://cips.cardano.org/cip/CIP-33).

### Scott Encoding

Scott encoding is a method for encoding datatypes in lambda calculus.
The Plutus Tx compiler adopts Scott encoding for Plutus Tx datatypes when compiling to Plutus Core 1.0.0.
When compiling to Plutus Core 1.1.0, sums of products is used instead, which makes scripts smaller and cheaper compared to Scott encoding.
Currently, Plutus V1 and V2 are only compatible with Plutus Core 1.0.0, whereas Plutus V3 is also compatible with Plutus Core 1.1.0.
However, we plan to make all Plutus ledger language versions compatible with all Plutus Core versions in the future.

For more details, see the [Wikipedia page](https://en.wikipedia.org/wiki/Mogensen%E2%80%93Scott_encoding) on Scott encoding.

### Script Context

An input to a Plutus script created by the ledger.
It includes details of the transaction being validated.
Additionally, since a transaction may do multiple things, each of which needs to be validated by a separate script, the script context also specifies what exactly the current script is responsible for validating.

### Sums of Products

Sums of products is an alternative method to Scott encoding for encoding datatypes.
The Plutus Core language supports sums of products since version 1.1.0.
Currently, Plutus Core 1.1.0 is only compatible with Plutus V3, but we plan to make it compatible with Plutus V1 and V2 in the future.

For more details, see [CIP-85](https://cips.cardano.org/cip/CIP-0085).

### Typed Plutus Core

The typed counterpart of Untyped Plutus Core, and can serve as a low-level IR for compilers targeting Untyped Plutus Core.
See [Plutus Core and Plutus Tx](./essential-concepts/plutus-core-and-plutus-tx.md).

### Untyped Plutus Core

A low-level language for on-chain code, based on untyped lambda calculus, a well-studied formalism for computing.
See [Plutus Core and Plutus Tx](./essential-concepts/plutus-core-and-plutus-tx.md).

### UTXO

UTXO stands for unspent transaction output.
Cardano adopts the UTXO model, one of the two popular ledger models for blockchains, the other one being the account model.
