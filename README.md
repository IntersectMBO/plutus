# Plutus Platform for Cardano

This repository contains the various components and some documentation for the Plutus Platform, providing smart contract functionality for the Cardano blockchain.

## Building

`default.nix` defines a package set containing all the packages in this repository. These can be built directly.
For example:
```
nix build -f default.nix language-plutus-core
```

The Plutus Core specification is also built this way, as the attribute `plutus-core-spec`.

## Docs

Docs are built by hydra. The latest docs for plutus core master branch can be found at
https://hydra.iohk.io/job/serokell/plutus/language-plutus-core.x86_64-linux/latest

You can also build the docs yourself locally. For example:
```
nix build -f default.nix language-plutus-core.doc
```
