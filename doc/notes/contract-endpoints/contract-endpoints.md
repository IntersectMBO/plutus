# Contract Endpoints and Blockchain Triggers

What we need to know for smart contracts

## Current State

### Blockchain triggers

Blockchain triggers are a way for client code to react to blockchain events automatically, similar to event handlers. 

Events are predicates on 
* funds at address within some range
* current slot within some range
* any combination of the two

Example: Funds at address _x_ are between 200 and 300 Ada, AND we have not reached slot _y_ yet.

By requiring clients to tell the wallet which addresses to watch we avoid having to keep track of the entire UTXO set all the time. 

Contracts can freely define event triggers using these predicates, and register handlers for them. The conditions of each registered trigger should be checked whenever the UTXO set changes.

When reacting to a blockchain event (in the event handler) we need access to the relevant parts of the UTXO set, including any data scripts of pay-to-script transaction outputs.

### Endpoints

* Contract endpoints are functions that take a number of parameters (to be supplied by the user) and return an action on the WalletAPI monad
* The types of the parameters depend on the contract. But we can generate schema information about them. Currently the schema is provided in a custom format but that will change to GraphQL.
* The set of endpoints for a given contract stays the same during the entire operation of the contract.

## Future

Some sensible extensions to the current system.

### Blockchain Triggers

There is currently no way to unregister a trigger. Some of them can be garbage collected automatically if they refer to a slot range in the past, but presumably we will need a more general way to delete them. This could involve:

* Giving the user some kind of handle when they register it, or
* Deleting them after they have been run once. Users can then register the trigger again in the handler code, if they want to.

It might also be useful to define an event trigger on a specific *output* (as opposed to an address), and be alerted whenever that output is spent.

### Contract Endpoints

In the future the endpoints should be a bit more dynamic. There is currently no 
distinction between a running contract (contract instance) and the definition 
of the contract. If we add the notion of a "contract instance" we can

* Display instance-specific status information to the user. For example if I enter a swap contract twice, with different parameters, then I would like to see how valuable each instance is.
* Change the actions available to a users depending on the state of the instance. For example, if I am close to breaking my margin agreement in the swap.
