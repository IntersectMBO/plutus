---
sidebar_position: 20
---

# Plutus-Related CIPs

This page lists all Cardano Improvement Proposals (CIPs) that are substantially related to Plutus smart contract platform, including core language features, builtin functions, and infrastructure improvements.

| CIP | Description | Status |
|-----|-------------|--------|
| [031](https://cips.cardano.org/cip/CIP-0031) | **Reference inputs** - Allows looking at outputs without spending them, crucial for Plutus validators | Active |
| [032](https://cips.cardano.org/cip/CIP-0032) | **Inline datums** - Allows datums to be attached directly to outputs instead of datum hashes | Active |
| [033](https://cips.cardano.org/cip/CIP-0033) | **Reference scripts** - Allows scripts to be attached to outputs for reuse without including in transactions | Active |
| [035](https://cips.cardano.org/cip/CIP-0035) | **Changes to Plutus Core** - Defines the process for proposing changes to Plutus Core, its builtins, and ledger interface | Active |
| [040](https://cips.cardano.org/cip/CIP-0040) | **Collateral Output** - Addresses collateral requirements for Plutus smart contract execution | Active |
| [042](https://cips.cardano.org/cip/CIP-0042) | **New Plutus Builtin serialiseData** - Adds builtin for serializing BuiltinData to BuiltinByteString | Active |
| [049](https://cips.cardano.org/cip/CIP-0049) | **ECDSA and Schnorr signatures in Plutus Core** - Adds cryptographic signature verification builtins | Active |
| [057](https://cips.cardano.org/cip/CIP-0057) | **Plutus Contract Blueprint** - Machine-readable specification for documenting Plutus contracts | Active |
| [058](https://cips.cardano.org/cip/CIP-0058) | ~~**Plutus Bitwise Primitives** - Superseded by CIP-121 and CIP-122~~ | Inactive |
| [068](https://cips.cardano.org/cip/CIP-0068) | **Datum Metadata Standard** - Token metadata standard using output datums, mentions "inspectable metadata from within Plutus validators" | Proposed |
| [069](https://cips.cardano.org/cip/CIP-0069) | **Script Signature Unification** - Unifies script signature handling across different script types | Active |
| [085](https://cips.cardano.org/cip/CIP-0085) | **Sums-of-products in Plutus Core** - Adds algebraic data type support to Plutus Core | Active |
| [091](https://cips.cardano.org/cip/CIP-0091) | **Don't force Built-In functions** - Optimization for builtin function evaluation | Proposed |
| [101](https://cips.cardano.org/cip/CIP-0101) | **Integration of keccak256 into Plutus** - Adds Keccak-256 hash function builtin | Proposed |
| [109](https://cips.cardano.org/cip/CIP-0109) | **Modular Exponentiation Built-in for Plutus Core** - Adds modular exponentiation builtin | Proposed |
| [110](https://cips.cardano.org/cip/CIP-0110) | **Plutus v1 Script References** - Enables reference scripts for PlutusV1 | Active |
| [112](https://cips.cardano.org/cip/CIP-0112) | **Observe Script Type** - Allows scripts to observe their own type during execution | Proposed |
| [117](https://cips.cardano.org/cip/CIP-0117) | **Explicit script return values** - Improves script return value handling | Active |
| [121](https://cips.cardano.org/cip/CIP-0121) | **Integer-ByteString conversions** - Adds integer to bytestring conversion builtins | Active |
| [122](https://cips.cardano.org/cip/CIP-0122) | **Logical operations over BuiltinByteString** - Adds bitwise logical operations | Active |
| [123](https://cips.cardano.org/cip/CIP-0123) | **Bitwise operations over BuiltinByteString** - Bitwise shift and rotation operations | Active |
| [127](https://cips.cardano.org/cip/CIP-0127) | **ripemd-160 hashing in Plutus Core** - Adds RIPEMD-160 hash function builtin | Active |
| [132](https://cips.cardano.org/cip/CIP-0132) | **New Plutus Builtin dropList** - Adds dropList builtin function | Proposed |
| [133](https://cips.cardano.org/cip/CIP-0133) | **Plutus support for Multi-Scalar Multiplication over BLS12-381** - Adds BLS12-381 multi-scalar multiplication | Proposed |
| [138](https://cips.cardano.org/cip/CIP-0138) | **Plutus Core Builtin Type - Array** - Adds Array as a builtin type | Proposed |
| [141](https://cips.cardano.org/cip/CIP-0141) | **Web-Wallet Bridge - Plutus wallets** - Wallet bridge specification specifically for Plutus-enabled wallets | Proposed |
| [152](https://cips.cardano.org/cip/CIP-0152) | **Modules in UPLC** - Introduces module system to Untyped Plutus Core | Proposed |
| [153](https://cips.cardano.org/cip/CIP-0153) | **Plutus Core Builtin Type - MaryEraValue** - Adds MaryEraValue as a builtin type | Proposed |
| [156](https://cips.cardano.org/cip/CIP-0156) | **Plutus Core Builtin Function - multiIndexArray** - Adds multi-dimensional array indexing builtin | Proposed |
| [381](https://cips.cardano.org/cip/CIP-0381) | **Plutus support for Pairings over BLS12-381** - Adds elliptic curve pairing operations for cryptography | Active |
