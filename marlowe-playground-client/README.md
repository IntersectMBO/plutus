# Marlowe Playground Client

## Getting started

Make sure you have a local backend server running first:
```bash
$(nix-build -A marlowe-playground.server-invoker)/bin/marlowe-playground webserver
```

Now we will build and run the front end:
```bash
# First generate the purescript bridge files
$(nix-build -A marlowe-playground.server-invoker)/bin/marlowe-playground psgenerator ./marlowe-playground-client/generated
# Now we will build and run the client on localhost
cd marlowe-playground-client
# Download javascript dependencies
yarn
# Install purescript depdendencies
yarn purs:compile
```

Then run `yarn run webpack:server` for an auto-reloading dev build on http://localhost:8009

## Adding dependencies

* Javascript dependencies are managed with yarn, so add them to [package.json](./package.json)
* purescript dependencies are managed with psc-package so add them to [psc-package.json](./psc-package.json)
* purescript uses package sets managed by spago so if the package set doesn't contain a dependency you can add it to [packages.dhall](./packages.dhall)

Whenever you change any of these files you should run `$(nix-build -A dev.scripts.updateClientDeps ../default.nix)/bin/update-client-deps` to make sure they are available to things that build purescript (such as webpack). Additionally running this script will make changes to various files that will need to be committed for CI to work.
