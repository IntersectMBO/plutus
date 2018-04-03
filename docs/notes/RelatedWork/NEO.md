# NEO

* [Website](https://neo.org)
* [White paper](http://docs.neo.org/en-us/index.html)
* [GitHub](https://github.com/neo-project)
* Account-based ledger
* Smart contracts: NeoContract based on the NeoVM aims to run any .NET and JVM languages (so far, only .NET is supported)
* Status: as of April 2018, running a public testnet 


## The blockchain architecture

* Proof-of-stake: [dBFT](http://docs.neo.org/en-us/node/whitepaper.html)
* Support for multiple (programmable) digital assets, digital identities, and smart contracts
* Implemented in C#

## NeoContract

There is a separate [NeoContract white paper](http://docs.neo.org/en-us/sc/white-paper.html).

Concerning smart contracts, the architecture has some similarities to [EOS](EOS.md) in that smart contract execution is one step removed from the blockchain and general code execution is supported. More precisely, the NeoVM is a stack-based VM in the tradition of the JVM and .NET CLR and aims to support a wide range of mainstream languages including Java, Kotlin, Go and Python. 

They implement these languages not by having dedicated compilers, but by translating the byte code of existing VMs, like .NET CLR and JVM. The current implementation seems only to support .NET CIL so far. In fact, to write smart contract code, you need to add a NeoContract plugin to Visual Studio, where you develop and compile the smart contract code.

The blockchain and the NeoVM are loosely coupled in that the blockchain exposes its functionality to smart contracts through a service API. In concrete terms, this is an SDK providing a class `SmartContract` from which all contracts inherit plus other classes that provide access to chain information (e.g., block height) as well as crypto functionality such as signature verification. The design seems fairly modular. They explicitly say that (a) NeoVM could be integrated with other blockchains and (b) that the NEO chain could use other VMs through that service API.

The integration with the chain is Ethereum-like. Each deployed contract is associated with an address. The address can be spent if a call to the associated contract code returns `true`. Contract execution is triggered when a transaction attempts to transfer funds out of an address associated with a contract. Moreover, smart contracts can be called directly from wallets (seems like an external call in Ethereum). Each smart contract address is also associated with a key-value store that can hold state for that contract. There is a mechanism for one contract to delegate modifying its state to another contract (sounds like Ethereum’s DELEGATECALL, but it may involve additional authorisation).

Generally, NEO contracts can call each other, *but* the inter-contract call tree must be statically know before the contract code is actually executed. This is to facilitate static decomposition of contract evaluation to facilitate the parallel execution of contract invocations that are independent (don’t modify the same store). This in particular, implies that inter-contract invocation cannot be recursive. However, code inside a single contract may use general recursion. (The exact mechanism by which they achieve having the inter-contract call information is fuzzy. They seem to use annotations in meta data at the moment, but also talk about static analysis.)

They do use a notion of gas, which is a separate currency minted over time for accounts that hold NEO in proportion to their NEO stake. Only some opcodes using storage, bandwidth, and/or expensive crypto operations seem to consume gas. They are also talking about letting some code run for free.