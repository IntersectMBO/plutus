# Plutus Application Backend

_PAB_ (Plutus Application Backend) is an Off-Chain application for managing the state of
Plutus contract instances.

## Table of Contents

- [Building](#building)
- [Running](#running)
- [PAB Components](#pab-components)

## Building

_PAB_ is a Cabal based Haskell project. Production builds are done with Nix using [haskell.nix](https://github.com/input-output-hk/haskell.nix)

### Cabal

```
$ cabal build
```

### Nix

```
$ nix-build ../default.nix -A plutus.haskell.packages.plutus-pab
```

## Running

In order to use PAB several of its components need to be started. Furthermore the pab-client has
to be started in order to access the web frontend. The required steps are described below.

First we build the startup scripts:

```
$ nix-build ../default.nix -A plutus-pab.demo-scripts
```

Next we start all required servers and install several contracts:

```
$ ./result/bin/pab-start-all-servers
```

Now we start an additional PAB connecting to the same node:

```
$ ./result/bin/pab-start-second-pab
```

Finally we can start the pab web frontend:

```
$ cd ../plutus-pab-client
$ npm start
```

The client is now running at https://localhost:8009 -- See [pab-demo-scripts.nix](https://github.com/input-output-hk/plutus/blob/pab-readme/plutus-pab-client/pab-demo-scripts.nix) for details on the service invcation and contract installation.

**Note**: By default the frontend will forward requests to `localhost:9080` - the first PAB instance. Connecting to the second
instance currently requires changing the proxy config in [webpack.config.js](https://github.com/input-output-hk/plutus/blob/master/plutus-pab-client/webpack.config.js#L33-L41). The second instance runs on port 9086 so the linked section in the config file would have to be
updated accordingly.

## PAB Components
PAB contains several commands and services, which are outlined below.

- [psgenerator](#psgenerator)
- [migrate](#migrate)
- [all-servers](#all-servers)
- [client-services](#client-services)
- [wallet-server](#wallet-server)
- [webserver](#webserver)
- [node-server](#node-server)
- [chain-index](#chain-index)
- [metadata-server](#metadata-server)
- [signing-process](#signing-process)
- [default-logging-config](#default-logging-config)
- [process-outboxes](#process-outboxes)

### psgenerator

```
$ cabal run plutus-pab -- psgenerator
```

#### Description

Generates the purescript bridge code.

#### Source

- [app/PSGenerator.hs](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/app/PSGenerator.hs)

### migrate

```
$ cabal run plutus-pab -- migrate
```

#### Description

Migrates the database in `pab-core.db` to the current schema.  The database contains the state for the eventful library. Please refer to the  [eventful docs](https://hackage.haskell.org/package/eventful-sqlite-0.2.0/docs/Eventful-Store-Sqlite.html) for more information.

#### Source
[Plutus.PAB.App.migrate](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Plutus/PAB/App.hs#L283)


#### all-servers

```
$ cabal run plutus-pab -- all-servers
```

#### Description

Combines the execution of all core services and mocks in the appropriate order:

* mocks
    - mock node
    - mock wallet
    - metadata
    - signing-progress
* core services
    - PAB webserver
    - chain index
    - process-outboxes

#### Dependencies

- plutus-pab.yaml
- sqlite database
- pab-client


#### Source

- [app/Main.hs](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/app/Main.hs#L246)

### client-services

```
$ cabal run plutus-pab -- client-services
```

#### Description

Starts all mocks and core services *except for* the mock node service:

* mocks
    - mock wallet
    - metadata
    - signing-progress
* core services
    - PAB webserver
    - chain index
    - process-outboxes

#### Dependencies

- plutus-pab.yaml
- sqlite database
- pab-client


#### Source

- [app/Main.hs](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/app/Main.hs#L262)

### wallet-server

```
$ cabal run plutus-pab -- wallet-server
```

#### Description

Plutus specific wallet implementation for managing user funds on the blockchain. Clients to this service are:

- PAB: adding funds to transactions & signing transactions
- user: making payments

#### Dependencies

- plutus-pab.yaml
- mock node

#### Source

- [Cardano.Wallet.API](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Cardano/Wallet/API.hs)
- [Cardano.Wallet.Server.main](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Cardano/Wallet/Server.hs#L101)
- [Cardano.Wallet.Types.Config](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Cardano/Wallet/Types.hs#L47)

### webserver

```
$ cabal run plutus-pab -- webserver
```

#### Description

Serves the PAB user interface

#### Dependencies

- plutus-pab.yaml
- sqlite database
- pab-client

#### Source

- [Plutus.PAB.Webserver.API](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Plutus/PAB/Webserver/API.hs#L23)
- [Plutus.PAB.Webserver.Server.main](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Plutus/PAB/Webserver/Server.hs)

### node-server

```
$ cabal run plutus-pab -- node-server
```

#### Description

Mock-implementation of a Goguen node. Clients to this service are:

- chain-index
- webserver
- mock wallet

#### Dependencies

- plutus-pab.yaml

#### Source

- [Cardano.Node.API.API](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Cardano/Node/API.hs)
- [Cardano.Node.Server.main](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Cardano/Node/Server.hs)

### chain-index

```
$ cabal run plutus-pab -- chain-index
```

#### Description

Provides a consistent view of the current state of the blockchain including a key-value store
for datum and script hashes. Clients to this service are:

- process-outboxes

#### Dependencies

- plutus-pab.yaml
- mock node

#### Source

- [Cardano.ChainIndex.API.API](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Cardano/ChainIndex/API.hs)
- [Cardano.ChainIndex.Server.main](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Cardano/ChainIndex/Server.hs#L69)

### metadata-server

```
$ cabal run plutus-pab -- metadata-server
```

#### Description

Key-Value store for user-defined data (mock implementation)

#### Dependencies

- plutus-pab.yaml

#### Source

- [Cardano.Metadata.API.API](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Cardano/Metadata/API.hs)
- [Cardano.Metadata.Server.main](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Cardano/Metadata/Server.hs#L196)

### signing-process

```
$ cabal run plutus-pab -- signing-process
```

#### Description

Attaches signatures to transactions so that they can be sent to the node. Clients to this service are:

- PAB
- mock wallet

#### Dependencies

- plutus-pab.yaml

#### Source

- [Cardano.SigningProcess.API.API](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Cardano/SigningProcess/API.hs#L11)
- [Cardano.SigningProcess.Server.main](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Cardano/SigningProcess/Server.hs#L64)

### default-logging-config

```
$ cabal run plutus-pab -- default-logging-config
```

#### Description

Prints the default logging configuration to STDOUT

#### Source

- [app/Main.hs](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/app/Main.hs#L479)

### contracts process-outboxes

```
$ cabal run plutus-pab -- contracts process-outboxes
```

#### Description

A service that regularly lokks at the contract instances requests and handles them

#### Dependencies

- plutus-pab.yaml
- sqlite database
- pab-client

#### Source

- [Plutus.PAB.Core.processAllContractOutboxes](https://github.com/input-output-hk/plutus/blob/master/plutus-pab/src/Plutus/PAB/Core/ContractInstance.hs#L585)


