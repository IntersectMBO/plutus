---
sidebar_position: 5
---

# Environment Setup

Plutus Tx is a subset of Haskell, so configuring the development environment for Plutus Tx is similar to a regular Haskell environment setup.
However, there are a few additional requirements:

- Plutus Tx supports a specific major version of GHC (currently 9.6).
- You’ll need some specific packages, such as `plutus-tx` and `plutus-tx-plugin`, which are hosted on the [Cardano Haskell Package repository](https://github.com/IntersectMBO/cardano-haskell-packages) (CHaP), rather than Hackage, Haskell's default package archive.
- You'll also need a few C libraries such as `secp256k1` and `blst`, which are required by the `plutus-tx` library.

You can take care of all of the above requirements manually, but the recommended method is to use the Nix develop shell provided by the [plutus-tx-template repository](https://github.com/IntersectMBO/plutus-tx-template).
You can clone the repository and run `nix develop`.
The repository also includes a sample Cabal project, pre-configured to follow the Auction example, which you can immediately modify and explore.

Alternatively, you can bypass cloning by running `nix develop github:IntersectMBO/plutus-tx-template`.
For instructions on installing Nix, visit [nixos.org](https://nixos.org/download/).
