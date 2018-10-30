# Plutus Playgrounds

*Plutus Playgrounds* is a lightweight, easy-to-use, web-based environment for exploratory Plutus development. It facilitates the development and execution of Plutus contracts without the overhead of installing and maintaining a full development environment and blockchain testnet. Nevertheless, it is built around the original Plutus platform components, including the use of Plutus Core for on-chain contract code, and supports the full Plutus language. Hence, contracts developed with Plutus Playgrounds can eventually be deployed to the Cardano blockchain.


## User Interface

The user interface has two main panes (probably side-by-side): (1) the editor pane and (2) the mockchain pane.

### Editor pane

The editor pane comprises an (1) editor component (ideally including syntax highlighting for Haskell), (2) controls to submit code for type checking and compilation, and a feedback console textbox with error message and similar. If the editor component is sufficiently powerful, we would like to highlight error locations in the source code.

Optionally, support editing multiple source files by having a listbox (or similar control) to switch between different Haskell sources for editing.

### Mockchain pane

The mockchain pane has three major parts: (1) a list of wallets including controls to trigger contract endpoints (i.e., wallet endpoint functions), (2) a list of the current sequence of wallet events that the user wants to submit for execution, and (3) a visual representation of the mockchain state after the sequence of wallet events has been executed. The number of wallets as well as the initial funds at each wallet are user-defined. The number can be between 1 and some TBD fixed upper limit.

Optionally, provide introspection facilities for components of the mockchain visualisation, such as the included transactions and scripts, and also debugging information for rejected, invalid transactions and failed script execution.


## Protocol between the frontend and backend

We are using a stateless architecture. Hence, the entire frontend state (that affects contract execution) needs to be transmitted to the backend on each request. Central is the contract source code and the current sequence of *wallet events*. A wallet event comprises the name of a *wallet endpoint function* and a list of arguments matching the type of the wallet endpoint function. Wallet endpoint functions are those designated functions within a contract that can be invoked by the user of a wallet that has loaded the contract.

### Frontend state required for contract execution

1. The contents of all Plutus source modules. (Initially, this is one module; optionally, we will extend it to a list of modules subsequently.)
2. List of initial amount of ADA in each wallet. (The length of this list determines the number of wallets.)
3. List of wallet events.

### Wallet events

The wallet events are invocations of wallet endpoint functions (aka *contract endpoints*), where the wallet user provides arguments to the endpoint function. The user does so within the frontend UI, which requires a limit on the number and form of those arguments. We support the following types as arguments types for wallet endpoint function s:

* `String`,
* `PubKey`,
* integral types, and
* products of the above.

Products can be in the form of record datatypes with a single constructor. Wallet endpoint functions can, at most, have TBD arguments.

## Contracts

Every contract includes a module `Contract` that exports a main `contract` function. The `contract` function uses 

```
registerEndpoint :: EndpointFunction fn => fn -> IO ()
```

to register all contract endpoint functions provided by this contract. Moreover, it uses 

```
TBD event registration functions
```

to register the initial set of blockchain events that the contract reacts to.


