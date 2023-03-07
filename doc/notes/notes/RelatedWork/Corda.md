# Corda

* [Website](https://www.corda.net)
* [White paper](https://docs.corda.net/_static/corda-technical-whitepaper.pdf)
* [GitHub](https://github.com/corda)
* UTxO-based ledger, where values can be arbitrary state objects
* Smart contracts: anything that can generate JVM code (they favour Kotlin & Java)
* Status: as of June 2018, still in development

## The architecture

Corda doesn't use a single, linear blockchain. Instead, the ledger is partitioned into disjoint subsets controlled by *notaries*. It is the notaries' responsibility to achieve local consensus and prevent double-spending. Different notaries may be based on different consensus protocols. Transactions can only spend outputs from a single notary (to avoid the need for two-phase commits between notaries). In order for the domains of multiple notaries to interact, the involved states need to be handed over to a single notary first. As a result, this is somewhat like a collection of sidechains (without a main chain).

The architecture puts emphasis on letting notary domains be semi-private and on the integration with legacy systems, such as conventional SQL databases. As a consequence of the former, Corda requires the presence of identity services that admit users to the network and associate their identities with their crypto keys.

Corda does not rely on broadcasting or gossiping. Instead, it is based on point-to-point communication, with message delivery via a store-and-forward network. Multi-party, multi-step protocols are realised with what they call the *flow framework*. It transpiles (JVM bytecode) from blocking, direct-style structured messaging to an asynchronous, non-blocking style, whose intermediate states are regularly made persistent to be able to tolerate node restarts and upgrades.


## Smart contracts

Smart contracts are represented as JVM classes implementing a designated `Contract` interface, and are transmitted as *attachments* to transactions; i.e., they are communicated separately and identified by hash values. The `Contract` interface exposes a single function called `verify`. This function gets a transaction as its sole argument. If the transaction is valid, the function returns normally; otherwise, it throws an exception. As one validation operation can involve multiple state objects, the union of all contracts specified by these state objects needs to be considered for that one validation operation.

The attachments to transactions that contain JVM contract classes may also contain data objects as a means to inject external data into contract computations.

They consider the use of standard libraries and domain-specific languages to avoid the need for all contracts to be written from scratch in a general-purpose language.

Finally, Corda forbids JVM features that have the potential to make contrast execution not deterministic.
