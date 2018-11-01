# Plutus Platform for Cardano

This repository contains the various components and some documentation for the Plutus Platform, providing smart contract functionality for the Cardano blockchain.

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
nix build -f default.nix localPackages.language-plutus-core.doc
```

## Bazel

Currently there are a couple of things missing from the bazel conversion:

1. Cabal benchmarks haven't been converted to bazel targets yet
2. The tests in `./tests` haven't been added as targets
