# Plutus Playgrounds

*Plutus Playgrounds* is a lightweight, easy-to-use, web-based environment for exploratory Plutus development. It facilitates the development and execution of Plutus contracts without the overhead of installing and maintaining a full development environment and blockchain testnet. Nevertheless, it is built around the original Plutus platform components, including the use of Plutus Core for on-chain contract code, and supports the full Plutus language. Hence, contracts developed with Plutus Playgrounds can eventually be deployed to the Cardano blockchain.

The current version of this document sets out the minimal expectations for the v1.0 launch in addition with clearly labelled optional (nice to have, but not critical) functionality for v1.0.


## User Interface

The user interface has three main panes: (1) the *editor pane,* (2) the *wallet pane,* and (3) the *transactions pane.*

### Editor pane

The editor pane comprises an (1) editor component with syntax highlighting for Haskell, (2) a button to submit code for type checking and compilation, and (3) a feedback console textbox with error messages and similar. If the editor component is sufficiently powerful, an optional feature is to highlight error locations in the source code. In this case, clicking on or hovering over an error should bring up the detailed error message.

Code is type checked and compiled when the corresponding button is clicked. Optionally, the edit component should submit code for type checking (only) whenever the user stops interacting with the editor pane for 0.5-1s after having made a change to the source code.

Optionally, this component should support editing multiple source files by having a listbox (or similar control) to switch between different Haskell sources for editing.

### Wallet pane

The wallet pane has two major parts: (1) a list of wallets with funds and including controls to trigger contract endpoints (i.e., wallet endpoint functions) and (2) a list of the current sequence of wallet events that the user wants to submit for execution. The list of wallets contains at least one and at most 10 wallets. It is accompanied by a "+' button to add additional wallets (greyed out once 10 wallets are displayed). Moreover, the wallet pane contains a "Replay Events" button. It triggers execution of the event sequence, generating transactions in the process.

Each wallet includes the following components:

* **Wallet name:** a string that can be edited by the user;
* **Wallet funds:** amount in ADA that can be edited by the user (this is the amount at genesis; i.e., start of the emulation); and
* **Contract endpoints:** These are zero to ten labelled buttons. The labels in all wallets are the same and they are the function names of the contract endpoints defined in the current contract.

The list of current wallet events is an unbound, possibly empty list of sequentially linked events. Each event includes the following components:

* **Event name:** the name of the contract endpoint associated with this event;
* **Wallet name:** the wallet that this event originated from;
* **Close button:** clicking this button deletes the corresponding event from the list; and 
* **Event arguments:** zero to ten key-value pairs. The keys are just string labels, but the values may be structured. The minimal requirement is that the values are multiline strings. Optionally, we render them either as a string or a nested list of key-value pairs (depending on the type of the corresponding argument of the contract endpoint).

When the user clicks a contract endpoint button in a wallet, a corresponding event is appended to the sequence of wallet events. The wallet name is set to the wallet whose button was clicked. The event arguments are initialised to default empty arguments, where appropriate.

Optionally, the individual events in the sequence of wallet events can be reordered by dragging them around.

The wallet pane is only active after the current contract has been compiled successfully. In fact, only in this case is the correct set of wallet endpoints known. Execution of the event sequence may fail when one or more arguments to one or more events is not a legitimate value of the corresponding type of contract endpoint function. In this case, each event with malformed argument(s) ought to be tinted red, while all malformed argument(s) are highlighted.

### Transactions pane

The transactions pane has three major parts.

1. A visual representation of the transactions in the form of the UTxO graph. The UTxO graph consists of (a) nodes that represent individual (valid) transactions, (b) edges between nodes that represent (valid) input-output connections, and (c) unmatched outgoing edges that represent unspent transaction outputs.
2. The final assignment of funds to wallets. This may be a subsets of the overall funds, because some funds may be locked by scripts. Optionally, the wallets should be colour coded and edges paying funds to those wallets should use the same colour. Moreover, we may display the wallet funds as coloured bars whose relative length represents their relative (final) value.
3. A possibly empty list of *invalid* transactions, each of which indicates the reason for why it is invalid.

Optionally, provide introspection facilities for valid and invalid transactions and graph edges. In particular, to query information that helps with debugging and also includes rejected, invalid transactions and failed script execution. Moreover, show the points in the graph, where a blockchain trigger was activated for a wallet.


## Protocol between the frontend and backend

We are using a stateless architecture. Hence, the entire frontend state (that affects contract execution) needs to be transmitted to the backend on each request. Central is the contract source code and the current sequence of *wallet events*. A wallet event comprises the name of a *wallet endpoint function* and a list of arguments matching the type of the wallet endpoint function. Wallet endpoint functions are those designated functions within a contract that can be invoked by the user of a wallet that has loaded the contract.

### Frontend state required for contract execution

1. The contents of all Plutus source modules. (Initially, this is one module; optionally, we will extend it to a list of modules.)
2. List of initial amount of ADA in each wallet. (The length of this list determines the number of wallets.)
3. List of wallet events.

### Wallet events

The wallet events are invocations of wallet endpoint functions (aka *contract endpoints*), where the wallet user provides arguments to the endpoint function. The user does so within the frontend UI, which requires a limit on the number and form of those arguments. We support the following types as arguments types for wallet endpoint functions:

* `String`,
* `PubKey`,
* integral types, and
* products of the above.

Products can be in the form of record datatypes with a single constructor. Wallet endpoint functions can, at most, have ten arguments.

Optionally, support for arguments of any type covered by the `Generic` class. While the type class allows us to (de)serialise those values, we need a representation that can be entered by the user. One option would be to have special UI support for the types listed above and for everything else, the user needs to enter the corresponding JSON (as a power user feature).


## Contracts

Every contract includes a module `Contract` that exports a main `contract` function. The `contract` function uses 

```
registerEndpoint :: EndpointFunction fn => fn -> ContractInit ()
```

to register all contract endpoint functions provided by this contract. Moreover, it uses 

```
TBD event registration functions
```

to register the initial set of blockchain events that the contract reacts to.


## Open questions

* We may want to require the use of `SafeHaskell` for all contract code: https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/safe_haskell.html
