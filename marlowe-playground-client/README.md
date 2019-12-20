# Marlowe Playground Client

## Getting started

You must build the Z3 WASM and JS components first and copy them to `./z3w.wasm` and `./z3w.js`. TODO: get nix building this.

```bash
cd marlowe-playground-client
$(nix-build -A dev.scripts.updateClientDeps ../default.nix)
yarn run webpack
```

## Development mode

The project has a web worker which we need to build separately so we do:
```
yarn worker:dev
```
And in another window:
```
yarn webpack:server
```
We can now visit (https://localhost:8009/)[https://localhost:8009/] and the website will reload every time any code is changed.

## Adding dependencies

* Javascript dependencies are managed with yarn, so add them to [package.json](./package.json)
* purescript dependencies are managed with psc-package so add them to [psc-package.json](./psc-package.json)
* purescript uses package sets managed by spago so if the package set doesn't contain a dependency you can add it to [packages.dhall](./packages.dhall)

Whenever you change any of these files you should run `$(nix-build -A dev.scripts.updateClientDeps ../default.nix)` to make sure they are available to things that build purescript (such as webpack). Additionally running this script will make changes to various files that will need to be committed for CI to work.
