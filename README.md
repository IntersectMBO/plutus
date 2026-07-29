# [Plutus Core](https://github.com/IntersectMBO/plutus)

## Introduction

Plutus Core is the scripting language embedded in the Cardano ledger and forms the basis of the Plutus Platform, an application development platform for developing distributed applications using the Cardano blockchain.

For more information about the projects, see the [user-documentation](#user-documentation).

This repository contains:

* The implementation, specification, and mechanized metatheory of Plutus Core
* Plutus Tx, the compiler from Haskell to Plutus Core.

For people who want to **use** the project, please consult the [user-documentation](#user-documentation).

## Development

### How to develop and contribute to the project

Run `nix develop` to enter the development shell and you will be presented with a list of available commands.

**Please see [CONTRIBUTING](CONTRIBUTING.md) for comprehensive documentation on how to contribute to the project, including development and submitting changes.**

### How to submit an issue

Issues can be filed in the [GitHub Issue tracker](https://github.com/IntersectMBO/plutus/issues).

### How to depend on the project from another Haskell project

The `plutus` libraries are published via [CHaP](https://input-output-hk.github.io/cardano-haskell-packages/).
See the information there for how to use CHaP.
After setting it up you should just be able to depend on the `plutus` packages as normal and cabal will find them.

## Documentation

### User documentation

The main documentation is located [here](https://plutus.cardano.intersectmbo.org/docs/).

The haddock documentation is located [here](https://plutus.cardano.intersectmbo.org/haddock/latest).

The documentation for the metatheory can be found [here](https://plutus.cardano.intersectmbo.org/metatheory/latest).

### Talks

* [Functional Smart Contracts on Cardano (2020)](https://www.youtube.com/watch?v=MpWeg6Fg0t8): an overview of the ideas behind the Plutus Platform.
* [The Plutus Platform (2020)](https://www.youtube.com/watch?v=usMPt8KpBeI): an overview of the Platform as a whole (including the Application Framework) at the time.

### Specifications and design

* [Plutus Technical Report (draft)](https://plutus.cardano.intersectmbo.org/resources/plutus-report.pdf): a technical report and design document for the project.
* [Plutus Core Specification](https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf): the formal specification of the core language.
* [Extended UTXO Model](https://plutus.cardano.intersectmbo.org/resources/extended-utxo-spec.pdf): a design document for the core changes to the Cardano ledger.

### Academic papers

* [Unraveling Recursion](https://plutus.cardano.intersectmbo.org/resources/unraveling-recursion-paper.pdf): a description of some of the compilation strategies used in Plutus IR ([published version](https://doi.org/10.1007/978-3-030-33636-3_15)).
* [System F in Agda](https://plutus.cardano.intersectmbo.org/resources/system-f-in-agda-paper.pdf): a formal model of System F in Agda ([published version](https://doi.org/10.1007/978-3-030-33636-3_10)).
* [The Extended UTXO Model](https://plutus.cardano.intersectmbo.org/resources/eutxo-paper.pdf): a full presentation of the EUTXO ledger extension ([published version](https://doi.org/10.1007/978-3-030-54455-3_37)).
* [UTXOma: UTXO with Multi-Asset Support](https://plutus.cardano.intersectmbo.org/resources/utxoma-paper.pdf): a full presentation of the multi-asset ledger extension ([published version](https://doi.org/10.1007/978-3-030-61467-6_8)).
* [Native Custom Tokens in the Extended UTXO Model](https://plutus.cardano.intersectmbo.org/resources/eutxoma-paper.pdf): a discussion of the interaction of the multi-asset support with EUTXO ([published version](https://doi.org/10.1007/978-3-030-61467-6_7)).
* [Translation Certification for Smart Contracts](https://arxiv.org/abs/2201.04919):  a certifier of Plutus IR compiler passes written in Coq.

## Licensing

You are free to copy, modify, and distribute this software under the terms of the Apache 2.0 license.

See the [LICENSE](./LICENSE.md) and [NOTICE](./NOTICE.md) files for details.
