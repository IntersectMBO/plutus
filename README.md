# Plutus Platform for Cardano

This repository contains the various components and some documentation for the Plutus Platform, providing smart contract functionality for the Cardano blockchain.

## Communication

Talk to us! We're active on the [Cardano forum](https://forum.cardano.org/). Tag your post with the `plutus` tag so we'll see it.

Do use the Github issue tracker for bugs and feature requests, but keep other discussions to the forum.

## Building

`default.nix` defines a package set containing all the packages in this repository. These can be built directly.
For example:
```
nix build -f default.nix localPackages.language-plutus-core
```

The Plutus Core specification is also built this way, as the attribute `docs.plutus-core-spec`.

### Binary caches

You may wish to add the IOHK binary cache to your Nix configuration. This will speed up builds a lot, since many things will have
been built already by our CI.

Put the following in `/etc/nix/nix.conf`, or `~/.config/nix/nix.conf` if you are a trusted user (if you don't know what that means, just use `/etc/nix/nix.conf`):
```
substituters        = https://hydra.iohk.io https://cache.nixos.org/
trusted-public-keys = hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ= cache.nixos.org-1:6NCHdD59X431o0gWypbMrAURkbJ16ZPMQFGspcDShjY=
```

## Docs

Docs are built by hydra. The latest docs for plutus core master branch can be found at
https://hydra.iohk.io/job/serokell/plutus/language-plutus-core.x86_64-linux/latest

You can also build the docs yourself locally. For example:
```
# Haddock for language-plutus-core
nix build -f default.nix localPackages.language-plutus-core.doc
# Combined Haddock for all our packages
nix build -f default.nix localPackages.combined-haddock
```

### Deploying the docs

The combined Haddocks are deployed to the [Github Pages page](https://input-output-hk.github.io/plutus/).

Deploying the docs means committing to the `gh-pages` branch. You can do this automatically
by running `./deploy-docs.sh`, and pushing the result if it looks good.

## Glossary

Definitions of some technical terms and names used throughout this project.

- Extended UTxO
    - The ledger model on which the Plutus Platform is based.
- On-chain code
    - Code written as part of a smart contract which executes on the chain during
      transaction validation.
- Off-chain code
    - Code written as part of a smart contract which executes off the chain, usually
      in a user's wallet.
- Plutus Core
    - A small functional programming language designed to run as on-chain code.
- Plutus IR
    - An intermediate language that compiles to Plutus Core, for use as a target
      language for compiler writers.
- Plutus Platform
    - The combined software support for writing smart contracts, including:
        - Libraries for writing off-chain code in Haskell.
        - Libraries for writing on-chain code in Plutus Tx.
        - Emulator support for testing smart contracts.
- Plutus Tx
    - A subset of Haskell which is compiled into Plutus Core.
