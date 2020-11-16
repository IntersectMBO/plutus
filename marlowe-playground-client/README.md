# Marlowe Playground Client

## Getting started

Make sure you have a local backend server running first:
```bash
$(nix-build -A marlowe-playground.server-invoker)/bin/marlowe-playground webserver
```

Check the [backend documentation](../marlowe-playground-server/README.md) for more information on how to setup the Github OAuth application.

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

Then run `yarn run webpack:server` for an auto-reloading dev build on https://localhost:8009

## Adding dependencies

* Javascript dependencies are managed with yarn, so add them to [package.json](./package.json)
* purescript dependencies are managed with spago, so add them to [spago.dhall](./spago.dhall)
* spago uses the concept of package sets, so if a particular package is not on the set, or you want to override the version, you can add it to [packages.dhall](./packages.dhall)

Whenever you change any of these files you should run `$(nix-build -A dev.scripts.updateClientDeps ../default.nix)/bin/update-client-deps` to make sure they are available to things that build purescript (such as webpack). Additionally running this script will make changes to various files that will need to be committed for CI to work.

## Code formatting

The code is formatted using [purty](https://gitlab.com/joneshf/purty), and there is a CI task that will fail if the code is not properly formatted. You can apply purty to the project by calling:

```bash
nix-shell shell.nix --run fix-purty
```

## VSCode notes

In order to have the PureScript IDE working properly with this project you need to open this folder as the root folder.
