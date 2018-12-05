# Building

## Server

### stack

```sh
cd plutus-playground-server
stack build
stack exec -- plutus-playground-server psgenerator ../plutus-playground-client/src/
stack exec -- plutus-playground-server webserver -p 8080 ../plutus-playground-client/dist/
```

### nix

```sh
nix-build -A plutus-server-invoker --option substituters https://hydra.iohk.io --option require-sigs false
/nix/store/***-plutus-server-invoker webserver -p 4000 ./plutus-playground/plutus-playground-client/dist
```

## Client

```sh
cd plutus-playground-client
yarn
yarn run bower install
```

Then run: `yarn run webpack` for a production build on http://localhost:8080
...or `yarn run webpack:server` for an auto-reloading dev build on http://localhost:8009

### nix

nix is not really suitable for development with purescript but if you want to check everything works correctly:

```sh
nix-build -A plutus-playground-purescript --option substituters https://hydra.iohk.io --option require-sigs false
nix-build -A plutus-playground-client  --option substituters https://hydra.iohk.io --option require-sigs false
```

## Docker image

```sh
nix-build -A plutus-playground-docker --option substituters https://hydra.iohk.io --option require-sigs false
docker load < /nix/store/***docker-image-plutus-playground-docker.tar.gz
# You can see the image name and tag as a result of the previous command and use it below
docker run -p 8080:8080 plutus-playground-docker:somecrazytag
```

# TroubleShooting

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
