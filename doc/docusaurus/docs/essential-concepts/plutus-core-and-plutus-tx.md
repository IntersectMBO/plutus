---
sidebar_position: 10
---

# Plutus Core and Plutus Tx

Understanding the roles and relationships between different languages is key to the effective and efficient development of smart contracts.

## Untyped Plutus Core

Untyped Plutus Core (UPLC), also known simply as Plutus Core or Plutus, is a low-level, Turing-complete language based on untyped lambda calculus, a simple and well-established computational model that dates back to the 1930s.
Thanks to its simplicity and extensive academic research, the need for updates or modifications to the language over time is minimal, ensuring long-term stability.
It also facilitates the creation of simple, formally verified evaluators.

Along with UPLC and its evaluator, we provide a compiler from Plutus Tx, a subset of Haskell, to UPLC.
However, UPLC can be an easy compilation target for any language that supports functional-style programming, in particular immutable data and higher-order functions, both of which are widely adopted today in programming languages, and are particularly suited to Cardano's UTXO ledger model, where UTXOs are immutable.

UPLC is the code that runs on-chain, i.e., by every node validating the transaction, using an interpreter known as the CEK machine.
A UPLC program included in a Cardano transaction is often referred to as a Plutus script or a Plutus validator.

### Typed Plutus Core and Plutus IR

Typed Plutus Core (TPLC) is the intrinsically typed counterpart of UPLC.
It is based on higher-order polymorphic lambda calculus (System Fω).
TPLC serves as a low-level intermediate representation (IR) for the Plutus Tx compiler.
TPLC is closely related to UPLC, and compiling TPLC into UPLC is simply a matter of erasing types.

Plutus IR (PIR) is a high-level IR also used by the Plutus Tx compiler.
It extends TPLC by adding recursive bindings and recursive data types.
The fact that recursion is explicitly in PIR, rather than encoded using fixed point operators as in TPLC and UPLC, makes PIR significantly more readable than TPLC and UPLC.
When optimizing the cost or size of Plutus scripts written in Plutus Tx, it is usually useful to look into PIR.

## Plutus Tx

Plutus Tx, the primary focus of this user guide, is a high-level language for writing the validation logic of the contract, the logic that determines whether a transaction is allowed to perform things such as spending a UTXO, minting or burning assets, and more.
Plutus Tx is not a new language, but rather a subset of Haskell, and it is compiled into UPLC.

There are several other high-level languages available as alternatives to Plutus Tx, all of which compile to UPLC.
See [Overview of Languages Compiling to UPLC](../delve-deeper/languages.md) for more information.

## Further reading

The formal details of Plutus Core are in its [specification](https://github.com/IntersectMBO/plutus#specifications-and-design).

The design is discussed in our [technical report](https://plutus.cardano.intersectmbo.org/resources/plutus-report.pdf).

PIR is discussed in [_Unraveling recursion: compiling an IR with recursion to System F_](https://iohk.io/en/research/library/papers/unraveling-recursion-compiling-an-ir-with-recursion-to-system-f/).