# plutus-contract-exe

A library for turning Plutus contracts into executables that implement the contract endpoints as an HTTP interface.

The `/examples` folder contains some hand-written examples for the use cases we currently have.

## Building the examples

1. `nix build -f default.nix localPackages.plutus-contract-exe` 

Alternatively:

1. `cd plutus-contract-exe`
2. `nix-shell`
3. `cabal build <name-of-example>` for example `cabal build contract-exe-guessing-game`

## Docker

To build the docker image for the guessing game contract:

1. `nix build -f default.nix plutus-contract-exe.docker`
2. `docker load -i result`
