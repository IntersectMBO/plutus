# Building

## Server

Please view the instructions for building the server [here](../plutus-playground-server/README.md).

## Client

```sh
# First generate the purescript bridge files
$(nix-build -A plutus-playground.server-invoker)/bin/plutus-playground psgenerator ./plutus-playground-client/generated
# Now we will build and run the client on localhost
cd plutus-playground-client
# Download javascript dependencies
yarn
# Install purescript depdendencies
yarn purs:compile
```

Then run `yarn run webpack:server` for an auto-reloading dev build on https://localhost:8009

You may also want to run `yarn run purs:ide` to start `psc-ide`
support running with the correct paths.

## Adding dependencies

* Javascript dependencies are managed with yarn, so add them to [package.json](./package.json)
* purescript dependencies are managed with psc-package so add them to [psc-package.json](./psc-package.json)
* purescript uses package sets managed by spago so if the package set doesn't contain a dependency you can add it to [packages.dhall](./packages.dhall)

Whenever you change any of these files you should rerun `$(nix-build -A dev.scripts.updateClientDeps ../default.nix)` to make sure they are available to things that build purescript (such as webpack). Additionally running this script will make changes to various files that will need to be committed for CI to work.

## nix

Fair warning before we start: You may struggle with PureScript on Nix on OSX.

The client and server can be built from the top-level of this repo with:

When building the client make sure that the generated directory is removed completely or you will get _Duplicate module_ errors.

```sh
nix-build \
  --option trusted-public-keys "hydra.iohk.io:f/Ea+s+dFdN+3Y/G+FDgSq+a5NEWhJGzdjvKNGv0/EQ=" \
  --option substituters https://hydra.iohk.io \
  -A plutus-playground.client -A plutus-playground.server-invoker
```

(You may prefer to put those option flags in your global =nix.conf= file.)

## Docker image

```sh
nix build -f default.nix plutus-playground.docker
docker load < result
# You can see the image name and tag as a result of the previous command and use it below
docker run -p 8080:8080 plutus-playground-docker:somecrazytag
```

# Troubleshooting

On a Mac, you may see this when compiling a contract:

```
GhcException "unable to load package `integer-gmp-1.0.2.0'"
```

This is due to a [GHC
bug](https://ghc.haskell.org/trac/ghc/ticket/15105). Sadly this isn't
slated to be fixed until GHC 8.8 at the earliest, but there's a simple
workaround (listed in that ticket):

``` sh
find ~/.stack -name HSinteger-gmp-1.0.2.0.o -ok rm {} \;
```
