# Meadow Client

## Getting started

```bash
cd meadow-client
$(nix-build -A dev.scripts.updateClientDeps ../default.nix)
yarn run webpack
```

## Adding dependencies

* Javascript dependencies are managed with yarn, so add them to [package.json](./package.json)
* purescript dependencies are managed with psc-package so add them to [psc-package.json](./psc-package.json)
* purescript uses package sets managed by spago so if the package set doesn't contain a dependency you can add it to [packages.dhall](./packages.dhall)

Whenever you change any of these files you should run `$(nix-build -A dev.scripts.updateClientDeps ../default.nix)` to make sure they are available to things that build purescript (such as webpack). Additionally running this script will make changes to various files that will need to be committed for CI to work.
