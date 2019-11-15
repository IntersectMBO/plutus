# Smart Contract Backend

## Part 1. System Description
The Smart Contract Backend (SCB) is a piece of software that manages the client-side execution of Plutus smart contracts. It acts as an intermediary between compiled Plutus contracts and the external processes that provide the resources needed by Plutus contracts, for example node clients, user interfaces, and crypto-related functions (keystores, etc). Apart from brokering messages, the SCB is responsible for maintaining contract state and validating user inputs.

[diagram of the components]

### 1.1 What are compiled Plutus Contracts

Conceptually, Plutus contracts are state machines - functions `(s,i) -> s` for inputs of type `i` and states of type `s`. An instance of a contract is a value of `s`. The type `s` contains contract-internal data (not interpreted by the SCB) as well as the event handlers that the contract has currently registered (interpreted by the SCB - see section 1.2.1). It is through the event handlers that the contract’s effects are expressed. From the Smart Contract Backend’s perspective, Plutus contracts are compiled Haskell programs that all have the same interface: They expect as input the previous state and a new event, and produce as output the new state.

The SCB maintains a set of Plutus contracts that it knows about, and for each of those contracts it manages zero or more instances. New contracts, as well as new instances for existing contracts, are added through user interaction.

The SCB advances each contract instance by doing the following:

1. Examine the current state of type s to get a list of event handlers that the instance wants to register
2. Forward each trigger to the appropriate process. For example, a trigger waiting for user input is forwarded to the UI, and a trigger issuing a new transaction is forwarded to the signing process (see Section X for details)
3. As soon as an event for one of the instance's event handlers is received to (for example, when the user clicked a button), the SCB forwards that event to the contract, along with the current state of the instance, producing the new state.
4. The SCB saves the new state and then goes back to step (1).

A contract instance is finished when the list of event handlers in step (1) is empty.

Note that steps 2 and 3 introduce concurrency by acting on whichever event is received first, without waiting for the other active event handlers. The contract however has a strictly sequential view of events, because it sees them one at a time, updating the state after each new event. See section [Concurrency] for details.

### 1.2 Message Format

The format of messages handled by the SCB is JSON. For each Plutus contract there exists a schema in form of an IOTS type definition that specifies the message types accepted and produced by the contract. (IOTS is a TypeScript library for describing types and validating JSON objects against them).

If a Plutus contract has the type `(s,i) -> s` in Haskell, then its IOTS schema describes the JSON representation of the two top-level types `(s,i)` and `s`, and of all their constituents.

The type s (contract state) looks like this in Haskell: `data ContractState = ContractState { handlers :: EventHandlers, state :: State }`. The state field contains contract-internal data. The SCB does not interpret the content of state, but it is expected to save the value and feed it back to the contract when the next event is received.  The triggers field is what the SCB uses in step (1) of the update procedure.

#### 1.2.1 Event Handlers

The `EventHandlers` type looks like `data EventHandlers = EventHandlers { slot :: Maybe Slot, endpoints :: [Endpoint], pendingTransactions :: [UnbalancedTx], ...  }`. Note that the exact set of fields depends on the contract. For example, there could be a contract that needs to make requests to an oracle, and these kinds of requests would be stored in an `oracleRequests` field. Or a contract that requires no interaction at all might not have an `endpoints` field. The `EventHandler` type of a given contract is described by that contract's IOTS schema.

The following five event handlers are required to support all the sample contracts that currently exist.

1. `Slot`: When the given slot is reached or has passed, send the current slot number to the contract.
2. `Endpoint`: Ask the user for input from the named endpoint. The user is expected to provide a value of the endpoint's type.
3. `SubmitTx`: Balance the transaction and sign it (see 1.3.2), then respond to the contract with the transaction's ID, then forward the signed transaction to the node client which sends it to the network.
4. `NextTransactionAt`: Start watching the address for changes and respond with the first transaction that changes the address (that is, the first transaction that spends or produces an output at the address)
5. `OutputsAt`: Respond to the client with a list of all unspent outputs that currently reside at the address.


#### 1.2.2 Events

The type `i` (input events) looks like `data Input = CurrentSlot Slot | TransactionSubmitted TxId | Endpoint Args | ...`. The exact number of constructors depends on the contract. A contract's `Input` type is related to its `EventHandlers` type in that every field in the `EventHandlers` record corresponds to one constructor of the `Input` type. Again, the `Input` type of a given contract is described by the contract's IOTS schema.

Q. How does the SCB know where to send an event handler?

### 1.3 External Processes

In the first version of the SCB, three external processes are supported: User-facing endpoints, a signing process, and a node client.

#### 1.3.1 UI

The SCB design enables an API consumer to generate UI elements for contract endpoints based on the IOTS schema, similar to how the Plutus Playground works currently.

#### 1.3.2 Signing

The transactions produced by Plutus contracts are unbalanced and unsigned (represented by the `UnbalancedTx` type). When the SCB encounters an unbalanced transaction during step (1) of the process, it needs to send it to several places. First, the transaction has to be balanced (incl. coin selection) and signed. Both tasks are performed by the signing process. Then the SCB informs the contract of the transaction ID and routes the transaction to a node client that in turn submits it to the blockchain.

#### 1.3.3 Node Client

The node client is a process that talks to a Cardano node. It can submit transactions to the blockchain and it can query the blockchain for information. There are three types of queries that the node client supports:

1. Stream all blocks to the SCB, including the `n` most recent blocks (where `n` is smaller than or equal to `k`, the number of blocks that may be rolled back (blockchain constant)). In practice, the SCB will maintain a connection to the node client throughout, and inspect every new block to check for triggers that have been registered by the contracts (see 1.2.1.4).
2. Ask for all unspent outputs at an address (see 1.2.1.5)
3. Ask for the current slot number (see 1.2.1.1)

We communicate with the node client using a REST API, and the listener will establish a web sockets connection and be updated regularly with accepted transactions.

The mock will implement the following endpoints (which will also be exposed by the real node):

```
--| Notations
    <-   Client sends to Server.
    ->   Server sends to Client.
    <d>  Datum `d` is JSON encoded.

data Update = Rollback Slot <Block>
            | NewBlock Slot <Block>

-- API
GET /utxo/:addr
-> <[(TxOutRef, TxOut)]>

GET /currentSlot
-> <Slot>

GET /chain/:slot -- Web sockets stream.
-> <Update> ..   -- A stream of updates.
(Possible error: `Specified slot outside of K range`)

POST /tx
<- <Tx>
(Lots of possible errors during transaction validation)
```

Notes:
1. If the node will try to sync beyond the K transactions limit, it will be impossible. If the node cannot properly sync, then it *may* make running contracts impossible.

#### 1.3.4 Endpoints

The user can call any one of the active endpoints by providing a JSON value that conforms with the endpoint's IOTS schema to the SCB. This value can be constructed via a UI or (in the first iteration) manually. Once an endpoint has been called, the SCB uses the endpoint's IOTS schema to validate the argument and then forwards it to the contract.

### 1.4 Failure Scenarios & Error Handling

* Connection between SCB and node client is lost: When the connection is restored, the SCB will ask the node client to stream the blocks that it has missed (see 1.3.3.1), unless the gap is larger than the rollback constant `k`. In that case it will only ask for the last `k` blocks.

TBD

### 1.5 Concurrency

## Part 2. Interactions

### 2.1 “Lock funds” flow

https://www.lucidchart.com/invitations/accept/9bc7ad38-ec3c-499c-abb9-952963fbf896

![](https://www.lucidchart.com/publicSegments/view/6978b4a8-0f89-4b0a-897c-818afce7ef95/image.png)
