# Building

## Server

### stack

```sh
cd playground-server
cp playground.yaml.sample playground.yaml

vi playground.yaml # Fill in this file.

stack build
stack exec -- plutus-playground-server psgenerator ../plutus-playground-client/src/
stack exec -- plutus-playground-server webserver ../plutus-playground-client/dist/
```

### nix

```sh
nix build -f default.nix plutus-playground.server-invoker 
result/bin/plutus-server-invoker webserver -p 4000 ./plutus-playground/plutus-playground-client/dist
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
