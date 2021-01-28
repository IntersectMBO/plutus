# PAB Client Interaction

Many Plutus apps want to bring their own UI and run the PAB in the background, possibly alongside other server processes.
Interactions between the frontend and the PAB use the PAB client HTTP API.
In this document we sketch a number of typical user flows involving the PAB client HTTP API.
We then apply this pattern to the Marlowe dashboard app.

## System description

On a high level we have the following components.

```plantuml
@startuml

interface "PAB client\nHTTP API" as pabclient

[Client app]  - pabclient
pabclient - [PAB]
[PAB] ..> [Cardano Node & wallet] : "monitor blockchain, submit transactions"

@enduml
```

The client app communicates with the Plutus application backend (PAB).
The PAB manages the state of Plutus contracts.
It connects to a Cardano node to receive notifications about transactions, and to a wallet that manages any funds that are used by contracts running on the PAB.

### Structure of the PAB

The internal state of the PAB consists of a chain index, a database, any number of contract instances, and a coordinating process called the runtime.

```plantuml

interface "PAB client\nHTTP API" as pabclient

package "PAB" {
  database "DB" as db

  [Contract instances]
  [PAB runtime]
  [Chain index] - [PAB runtime]
  [PAB runtime] <..> [Contract instances] : manage endpoints
  [PAB runtime] <..> db : store contract state
  pabclient - [PAB runtime]
}

[PAB runtime] ..> [Cardano node & wallet] : "monitor blockchain, submit transactions"
```

#### Chain index

The chain index maintains a consistent view of a subset of the blockchain.
It keeps track of a set of interesting unspent transaction outputs (UTXOs) and, crucially, of any datum and script values that were included in past transactions.
We often need preimage of a datum hash because it represents the on-chain state of a contract.
Such preimages may be submitted as part of Goguen transactions, but only their hashes stay in the UTXO set.
The values are discarded by the node.
Therefore the PAB maintains an index of datum values that it encountered.

#### Contract instances

Each of the contracts that are installed in the PAB can have zero or more *contract instances* running at any point in time.

PAB clients can start, stop and inspect contract instances using the PAB client HTTP API.

The PAB can be distributed with pre-installed contracts, and new contracts can be installed in the PAB at runtime.

For example, the Marlowe app has a PAB with a single contract pre-installed (the Marlowe contract).
This PAB will have many instances of that one contract.
It does not need to install any additional contracts at runtime.

#### Database

The chain index and contract instances state is saved in a sqlite database.

## User flows

In the following we describe some typical user flows, using the PAB client HTTP API.
Blue arrows indicate websocket communication.

### Starting a new instance of a contract

```plantuml

autonumber

participant "client app" order 1
participant PAB order 2
participant "contract instance" order 3

"client app" -> PAB: start new instance
PAB -> "contract instance": Start

autonumber stop
"contract instance" -> PAB

autonumber 3
PAB -> "client app": instance ID
"client app" -> "contract instance": open websocket
"contract instance" -[#0000ff]> "client app": status
```

1. The client app makes a request to the "new-instance" HTTP route. It expects two parameters: The wallet, and the contract ID.
2. The PAB runtime generates an instance ID and starts the instance.
3. The PAB runtime returns the instance ID to the client app.
4. The client app uses the instance ID to open a websocket connection on the PAB client HTTP API.
5. The contract instance starts sending updates to the client app.

### Calling a endpoint

```plantuml

autonumber

participant "client app" order 1
participant "contract instance" order 2

"contract instance" -[#0000ff]> "client app": status
note left of "client app"
The status message
includes a list of
active endpoints
end note
"client app" -> "client app": Select an endpoint to call
"client app" -[#0000ff]> "contract instance": Call endpoint
"contract instance" -[#0000ff]> "client app": status
```

1. The contract instance notifies the client app of the endpoints that are currently active.
2. The client app decides which of the endpoints to call.
3. The PAB performs the actual call on the instance and returns the result.

### Inspecting instance logs

The logs produced by the instance can be retrieved either via the HTTP API or via the websockets protocol.
Requests to the HTTP API always return the entire list of log messages of the instance.
Status updates delivered through the websocket protocol only include the new log messages that have been added since the last status update.

1. The user calls the "logs" route on the HTTP API, or
2. The PAB pushes instance logs to the user.

### Terminating an instance

1. Call "terminate" on the instance

## Marlowe dashboard app

The Marlowe dashboard is an application that uses the PAB to run multiple instances of the Marlowe contract.
The dashboard is hosted centrally (IOHK), allowing interested users to log in an try out some Marlowe contracts on the emulated blockchain.
It uses simulated Ada only, no real funds.
It is intended to be reset frequently, approx. every 24h.

### System description

The Marlowe dashboard has the following components.

```plantuml
@startuml

interface "PAB client\nHTTP API" as pabclient
interface "Mock node HTTP API" as mocknode

actor user

[Marlowe dashboard UI] -> [Marlowe app]

user - [Marlowe dashboard UI]
[Marlowe app]  - pabclient
[Marlowe dashboard UI] -> pabclient
pabclient -> [PAB]
[PAB] ..> [Mock node & wallet]
mocknode - [Mock node & wallet]
[Marlowe app]  -> mocknode

@enduml
```

On the right we have the PAB as before.
In this instance the PAB connects to a *mock node* instead of the real node.
The two Marlowe-specific components are the Marlowe dashboard UI and the Marlowe app.
The UI uses the PAB client API, in particular the websockets section of this API, to receive notifications about instances of the Marlowe contract that are managed by the PAB.
The UI *also* connects to the Marlowe app for session management.

#### Mock node

The mock node is an implementation of the node interface and the EUTXO-with-scripts-and-multi-asset ledger.
It does not have any kind of networking or consensus protocol.

#### Marlowe app

The Marlowe app manages active user sessions.
It uses the PAB client HTTP API to start instances of the Marlowe contract, and the mock node HTTP API to provide users with their initial funds.
Its internal state is a map of user session (cookie, etc.) to contract instance.

### Typical usage

From a user's perspective the interaction with the Marlowe dashboard begins as follows.

1. Open the Marlowe dashboard URL in the browser
2. Start a new session or resume an existing session
  * On starting a new session the Marlowe app generates a private/public key pair, representing the identity of the user. The Marlowe app then generates a transaction on the mock node that pays some predefined amount of simulated Ada to the new address. Then the Marlowe app calls on the PAB to start a new contract instance (using a mock wallet for the user's private/public key pair) and stores a reference to the contract instance ID together with the key pair. It returns the contract instance ID to the user.
  * On resuming a previous session the Marlowe app looks up the contract instance ID for that session and returns it to the user.
3. The user is then redirected to the Marlowe app UI for the contract instance.

This is the flow for starting a new session.

```plantuml
actor user order 1
participant MUI order 2
participant MAPP order 3
participant PAB order 4
participant node order 5

autonumber

user -> MUI: Start new session
MUI -> MAPP: Start new session
MAPP -> MAPP: Generate key pair
MAPP -> node: Start mock wallet
MAPP -> node: Generate initial tx
MAPP -> PAB: Start instance
note right of MAPP
Start a new instance of the Marlowe
contract using the mock wallet for
the user's key pair
end note
PAB -> MAPP: Instance ID
MAPP -> MAPP: Store instance ID
MAPP -> MUI: instance ID
MUI -> PAB: Connect instance ID
PAB -[#0000ff]> MUI: Status
MUI -> user: Status
note right of user
Show endpoints, user
can call endpoints,
etc.
end note
```

1. 