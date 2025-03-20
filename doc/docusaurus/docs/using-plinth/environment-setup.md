---
sidebar_position: 5
---

# Environment Setup

Plinth is a subset of Haskell, so configuring the development environment for Plinth is similar to a regular Haskell environment setup.
However, there are a few additional requirements:

- Plinth supports a specific major version of GHC (currently 9.6).
- You’ll need some specific packages, such as `plutus-tx` and `plutus-tx-plugin`, which are hosted on the [Cardano Haskell Package repository](https://github.com/IntersectMBO/cardano-haskell-packages) (CHaP), rather than Hackage, Haskell's default package archive.
- You'll also need a few C libraries such as `secp256k1` and `blst`, which are required by the `plutus-tx` library.

The best way to setup your environment is with the [plinth-template](https://github.com/IntersectMBO/plinth-template) repository. See its [README](https://github.com/IntersectMBO/plinth-template?tab=readme-ov-file#plinth-template) for complete instructions on how to get up and running using Docker, Nix, or a custom approach.
