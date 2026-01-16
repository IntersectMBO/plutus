---
sidebar_position: 10
---

# Different Notions of Version

There are several different notions of version that Cardano smart contract developers must distinguish.
For each Plutus script that is deployed on-chain, its execution behavior depends on protocol version, ledger language version and Plutus Core version (as well as the [cost model](../delve-deeper/cost-model))).
These all influence which syntax and semantics are available for UPLC scripts.

The ledger language version and Plutus Core version can be chosen by the script developer, while the protocol version is only changed by on-chain governance.
To develop for a given ledger language in Plinth, say PlutusV3, import the `PlutusLedgerApi.V3` module from the `plutus-ledger-api` package.
To control the Plutus Core version that Plinth targets, set the `target-version` [compiler option](../delve-deeper/plinth-compiler-options).

## Ledger Language Version

This is what "Plutus V1", "Plutus V2", "Plutus V3" refer to.
It is called "ledger" language version because they are _not_ really different versions of a language in the sense of programming languages, but different languages from the Cardano ledger's point of view; the ledger handles Plutus V1 vs. V2 vs. V3 differently.
In essence, "Plutus V1", "Plutus V2" and "Plutus V3" are tags that the ledger attaches to validators in a transaction.

From the ledger's perspective, they are in fact totally different languages:
there is no requirement that they be similar or compatible in any way.
However, the "V1", "V2" and "V3" naming scheme is practically useful because in reality they have a lot in common (e.g., the underlying language is Plutus Core and programs are executed by the Plutus Core evaluator, regardless of ledger language version); plus it makes it clear the order that they were introduced and the relationships among them.

When simply writing a standalone program, say one that takes two integers and returns their sum, or one that implements a Sudoku solver, the notion of ledger language version is completely irrelevant.
There is no need (and nowhere) to specify whether you are writing a Plutus V1, or Plutus V2, or Plutus V3 program - again, the concept of ledger language version does not apply to programs themselves.
You simply write your code in Plinth, compile it to UPLC, and run it with a UPLC evaluator.
This is what we mean by "they are not really different versions of a language in the sense of programming languages".

It is only when you write a Plutus _validator script_, put it in a transaction and submit it to the Cardano ledger, that ledger language version becomes relevant. It is relevant in three ways:

- Depending on the ledger language version, the ledger will pass different arguments to the validator.
  For instance, the arguments passed to a Plutus V2 validator include a list of reference inputs of the transaction. This is not passed to a Plutus V1 validator since reference inputs were introduced later than Plutus V1 (specifically, Plutus V1 was introduced in the Alonzo era, while reference inputs were introduced in the Babbage era).
  Similarly, only Plutus V3 can be used to validate governance actions, since governance actions are introduced in the Conway era and are not part of the pre-Conway era transactions, and thus aren't part of the arguments passed to Plutus V1 or V2 validators.
- At present, a newer ledger language version has access to more builtin functions than an older ledger language version.
  Bear in mind that this will change as we plan to make all builtin functions available to all ledger language versions.
- At present, Plutus Core version (explained below) 1.1.0 can only be used with Plutus V3, while Plutus V1 and V2 validators must use Plutus Core 1.0.0.
  This will also change, as we plan to make all Plutus Core versions compatible with all ledger language versions.

When do we introduce a new ledger language version?
A new ledger language version must be introduced when a new ledger era is rolled out, because in a new ledger era, transactions will be different and contain new and/or modified fields, such as governance actions introduced in the Conway era.
As a result, new information will need to be passed as arguments to Plutus validators.
This necessitates a new ledger language version, because the arguments passed to existing ledger language versions must stay exactly the same, so that existing validators continue to work.

Previously it was also the case that introducing new builtin functions or new Plutus Core versions necessitate a new ledger language version, but this is no longer the case.
Introducing a new ledger language version is very expensive as it must be maintained forever.
Going forward we expect the launch of new ledger eras to be the only reason for introducing new ledger language versions.

## Plutus Core Version

Plutus Core version is the usual sense of version pertaining to programming languages - in this instance the Plutus Core language.
So far there have been two Plutus Core versions: 1.0.0 and 1.1.0.
1.1.0 adds sums-of-products to the language by introducing two new AST node types: `Case` and `Constr`.
See [CIP-85](https://cips.cardano.org/cip/CIP-0085) for more details.

Note that adding new builtin functions does not require a new Plutus Core version.
Once a new builtin function is added, one can simply start using the new builtin function with an existing Plutus Core version.

## Protocol Version
The protocol version (PV) is a protocol parameter of the form `MAJOR.MINOR`, which is the main factor for determining available features and behavior of the chain.
That behavior is implemented in the node software (which includes the Plutus Core evaluator).
For example, starting with PV 11, the semantics of PlutusV3 + UPLC 1.1.0 is extended with [casing on constants](../delve-deeper/casing-constants).
This feature does not affect execution of older scripts, as the UPLC interpreter takes the associated PV into account.

Changes to protocol parameters are agreed upon by the decentralized governance model. A hard fork bumps the major part of the protocol version.
For more detail, see the [Cardano Developer Portal](https://developers.cardano.org/docs/governance/cardano-governance/)


## Builtin Semantics Variant

Depending on the protocol version or the ledger language version, or both, we may want to have different behavior of a particular builtin function.
For example, we might want to fix a bug but need to retain the old buggy behavior for old evaluations of already-submitted scripts, so we have to have a way of knowing which regime we are in.

One example is the builtin function `consByteString`.
If the first argument is outside of the range of `Word8`, the original behavior is to wrap it around.
The new behavior starting at Plutus V3 is to throw an exception.

When evaluating a standalone program using the `uplc` executable, flag `-S` or `--builtin-semantics-variant` can be used to inform the evaluator which semantics variant to use.

## Plutus Haskell Package Version

Several Plutus components are regularly released as libraries, such as `plutus-core`, `plutus-ledger-api` and `plutus-tx-plugin`.
These packages are published on the [Cardano Haskell Package repository](https://github.com/IntersectMBO/cardano-haskell-packages) (CHaP), rather than Hackage, Haskell's default package archive.
Each release has a version following a standard release versioning scheme, and this is completely orthogonal and irrelevant to all other aforementioned notions of version.
