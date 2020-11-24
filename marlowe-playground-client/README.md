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
npm install
# Install purescript depdendencies
npm run purs:compile
```

Then run `npm run webpack:server` for an auto-reloading dev build on https://localhost:8009

## Adding dependencies

* Javascript dependencies are managed with npm, so add them to [package.json](./package.json)
* purescript dependencies are managed with psc-package so add them to [psc-package.json](./psc-package.json)
* purescript uses package sets managed by spago so if the package set doesn't contain a dependency you can add it to [packages.dhall](./packages.dhall)

Whenever you change `psc-package.json` or `packages.dhall` you need to make sure that all dependencies can still properly be resolved and built.
You can do so using the `update-client-deps` script:

- Inside the nix-shell environment: `update-client-deps`
- Outside of the nix-shell environment (from the client directory): `$(nix-build -A plutus.updateClientDeps ../)/bin/update-client-deps`

The `update-client-deps` script will generate/update `.nix` files which have to be committed and are required for a successful CI run.

## Code formatting

The code is formatted using [purty](https://gitlab.com/joneshf/purty), and there is a CI task that will fail if the code is not properly formatted. You can apply purty to the project by calling:

```bash
nix-shell shell.nix --run fix-purty
```

## VSCode notes

In order to have the PureScript IDE working properly with this project you need to open this folder as the root folder.
