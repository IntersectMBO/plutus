# plutus-contract

A library for writing Plutus contracts and transforming them into executables that run on the app platform. The high-level workflow is this:

* Write a contract using the `Plutus.Contract` module. The type of contracts is `ContractActions r => Contract r ()`, where `PlutusContract r` describes the actions it can perform. `ContractActions` is a list of common contract actions that includes waiting for blockchain events, exposing endpoints, and waiting for user actions. See the definition of `Examples.Crowdfunding.crowdfunding` for an example.
* (optional) Write traces for the contract using the `Plutus.Contract.Emulator` module. Traces are sequences of actions by simulated wallets that use the contract. Their signature is `(MonadEmulator m) => ContractTrace m a ()`. See `Examples.Game.lockTrace` for an example.
* (optional) Write unit tests for the contract, using the `Spec.HUnit` module to make make assertions about traces.
* Turn the contract into an executable using the `Plutus.Contract.App` module. `run :: Contract (ContractEffects '[]) () -> IO ()` takes a contract and turns it into an HTTP server with two routes, `initialise` and `run`. `initialise` responds to `GET` requests with the initial state of the contract. `run` expects POST requests of the old state together with an input event, and produces the new state. `Plutus.Contract.App.runWithTraces` takes a list of named traces whose intermediate states can be printed by calling the program with the `trace` argument and the name of a trace. The intermediate states so printed are JSON values that can be used as arguments for the `run` endpoint.

The `/examples` folder contains some hand-written examples for the use cases we currently have.

Contracts are represented by the `Resumable f a` type from `Plutus.Contract.Resumable`. `f` describes the effects that the contract can have. From the user's point of view, `f` is a list of effects (from `extensible-effects`) defined in `Plutus.Contract.Effects` and sub-modules. Internally, before running the contract, the entire list of effects is converted to a single `Maybe i -> Either o a` function, where `i` is a union of all possible inputs to the contract, and `o` is an output describing what inputs are currently expected. For example, `o` could say "I am currently waiting to be notified of a change to address XYZ". In the `Plutus.Contract.App` module, as well as in the unit tests, `i` is fixed to `Plutus.Contract.Prompt.Event.Event` and `o` is `Plutus.Contract.Prompt.Hooks.Hooks`. Each instance of a contract is represented by a `Plutus.Contract.Record.Record` value, and the state can be advanced using `Plutus.Contract.Resumable.updateRecord`. See the note `[Handling state in contracts]` for details.

## Building the examples

1. `nix build -f default.nix localPackages.plutus-contract` 

Alternatively:

1. `cd plutus-contract`
2. `nix-shell`
3. `cabal build <name-of-example>` for example `cabal build contract-exe-guessing-game`

## Docker

To build the docker image for the guessing game contract:

1. `nix build -f default.nix plutus-contract.docker`
2. `docker load -i result`
