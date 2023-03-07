# Pay-to-contract Extension to Bitcoin Transactions

* [Proposal](https://github.com/oleganza/bitcoin-papers/blob/master/SmartContractsSoftFork.md)


## Summary

Adds the notion of a contract (in addition to conventional) Bitcoin scripts, which 

* may keep some state (a separate *contract stack*) across invocations,
* can inspect the transaction that they are validating (in particular, the amounts and scripts on all outputs), and
* inquire the sum of all funds payed towards a given output script hash.

This enables the definition of chains (or continuations) of contract scripts that together enforce a contract across multiple dependent transactions.