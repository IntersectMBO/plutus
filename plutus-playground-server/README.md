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
$(nix-build -A plutus-playground.server)/bin/plutus-playground-server webserver
```

## Testing

Tests should be run with nix:

```sh
nix build -L -f default.nix plutus.haskell.packages.plutus-playground-server.checks
```
