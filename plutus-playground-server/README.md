# Building

## Server

### stack

```sh
stack build plutus-playground-server
stack exec -- plutus-playground-server psgenerator ./plutus-playground-client/generated
stack exec -- plutus-playground-server webserver
```

### nix

```sh
$(nix-build -A plutus-playground.server-invoker)/bin/plutus-playground webserver
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
