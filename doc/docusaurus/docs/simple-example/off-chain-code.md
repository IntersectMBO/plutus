---
sidebar_position: 40
---

# Off-chain code

Since the main purpose of this example is to introduce Plutus Tx and Plutus Core, we walked through only the on-chain code, which is responsible for validating transactions (in the sense of determining whether a transaction is allowed to spend a UTXO).

In addition to the on-chain code, one typically needs the accompanying off-chain code and services to perform tasks like building transactions, submitting transactions, deploying smart contracts, querying for available UTXOs on the chain, etc.

<!-- TODO Correct the inaccurate info below about Plutus Apps -->

A full suite of solutions is [in development](https://plutus-apps.readthedocs.io/en/latest/plutus/explanations/plutus-tools-component-descriptions.html).
See the [plutus-apps](https://github.com/IntersectMBO/plutus-apps) repo and its accompanying [Plutus tools SDK user guide](https://plutus-apps.readthedocs.io/en/latest/) for more details.

Some other alternatives include [cardano-transaction-lib](https://github.com/Plutonomicon/cardano-transaction-lib) and [lucid](https://github.com/spacebudz/lucid). 
All these are based on the [Cardano API](https://github.com/IntersectMBO/cardano-api), a low-level API that provides the capability to do the off-chain work with a local running node.
