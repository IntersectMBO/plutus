# Sequence

* [Website](http://seq.com)
* [Documentation](https://dashboard.seq.com/docs)
* [GitHub](http://github.com/chain)


## Ledger

TBC


## TxVM (Transaction Virtual Machine)

* [TxVM whitepaper](https://chain.com/assets/txvm.pdf)

TxVM aims to marry the benefits of Bitcoin's declarative UTxO model with those of Ethereum's imperative account-based model. They do this to have a cleaner model of how the blockchain state progresses and also to retain the implicit parallelism of the UTxO model. The idea is that imperative contracts write a transaction log (instead of directly affecting the blockchain state). When a contract finalises its log, the log is committed to the blockchain state. In this model, only during transaction log application is there a sequentialisation due to manipulating a shared mutable state.

The machine model is quite complex, though, including the ability for contract code to manipulate other contracts (as stack objects) and to suspend contract execution in a variety of forms. Moreover, some stack objects and some stack operations are special as they need to obey some uniqueness properties (in dealing with contracts as objects and in dealing with assets on the stack).


## Smart contract language: Ivy

TBC