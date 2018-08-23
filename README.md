# Plutus Platform for Cardano

This repository contains the various components and some documentation for the Plutus Platform, providing smart contract functionality for the Cardano blockchain.

## Building

`default.nix` defines a package set containing all the packages in this repository. These can be built directly. 
For example:
```
nix build -f default.nix language-plutus-core
```

## Developing

An appropriate environment for developing a package can be entered using the `env` attribute of the package. For example:
```
nix-shell default.nix -A language-plutus-core.env
```

## Updating the generated Haskell package set

`pkgs/default.nix` contains a generated package set with all the dependencies for this projet.

You should regenerate this if you change any dependencies in cabal files. To do this, use the 
environment defined in `shell.nix`, and run `pkgs/generate.sh`.

## CI

The CI will build the projects, and also the tests in `default.nix`.

If you add a dependency to a `.cabal` file, you will need to run
`./pkgs/generate.sh` and commit the changes.

## Docs

Docs are built by hydra. The latest docs for plutus core master branch can be found at
https://hydra.iohk.io/job/serokell/plutus/language-plutus-core.x86_64-linux/latest

You can also build the docs yourself locally. For example:
```
nix build -f default.nix language-plutus-core.doc
```
