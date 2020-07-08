# Qtum

* [Website](https://qtum.org)
* [White paper](https://qtum.org/uploads/files/a2772efe4dc8ed1100319c6480195fb1.pdf)
* [GitHub](https://github.com/qtumproject)
* UTxO ledger
* Smart contracts: 
  1. Bitcoin Script
  2. Ethereum-compatible via Bitcoin Script integration opcodes
  3. Higher-level DSL with its own VM (future work)
* Status: as of April 2018, running mainnet


## The blockchain architecture

* Proof-of-stake: [PoS 3.0](http://blackcoin.co)
* Implemented in C++

## Smart contracts

Qtum transactions on the UTxO ledger use Bitcoin Script as usual, but extended with three additional opcodes that are used to trigger the execution of and interaction with scripts in EVM byte code. Qtum uses an *account abstraction layer* to translate between the UTxO ledger and accounts for the EVM. This is an interesting integration, but there are a tricky corners:

* They add three new Bitcoin Script opcodes, which are used in UTxO outputs and, when a transaction with such an output gets added to a block, the associated EVM code is executed. For one opcode that means that a new contract is created from the EVM code. For another opcode, it means that the output's funds are assigned to the EVM contract, which can spend them subsequently.

* Where things get complicated is that contract execution can trigger the creation of new (UTxO) transactions. The modified EVM intercepts internal contract calls and turns them into new transactions. These transactions aren’t transmitted on the P2P network as usual, but only processed locally (but each node should produce the same transactions during contract execution, so they stay in sync). My impression is that these internally created transactions need to be added to the same block as the transaction that spawned them, but I am not completely sure about that. (And it seems fragile as blocks might grow beyond their maximum size. The exact behaviour wasn't immediately clear from the white paper.)

* Moreover, they have got an intricate system for dealing with gas and in particular refunding unspent gas and paying the fees of out-of-gas execution of contracts to miners. It involves adding additional outputs to the coinbase transaction of the current block. This again can lead to a block growing beyond its maximum allowed size, so there are some mechanisms to delay some of the outputs to the next block if I understood correctly.
