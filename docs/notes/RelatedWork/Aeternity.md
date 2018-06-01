# Æternity

* [Website](https://www.aeternity.com/)
* [White paper](https://aeternity.com/aeternity-blockchain-whitepaper.pdf)
* [Video summary focusing on smart contracts](https://youtube.com/watch?v=VXsqvfPIdWg)
* [GitHub](https://github.com/aeternity/)
* Account-based ledger
* Three types of smart contracts: 
  1. Varna: Bitcoin-script like, but with functional syntax and types — part of transaction validation
  2. Sophia: ML dialect — for off-chain contracts in state channels
  3. Solidity: runs in modified (for increased safety and versatility) EVM to simplify porting from Ethereum
* Status: as of March 2018, running a testnet 


## The blockchain architecture

* Implemented in Erlang (team includes several well known Erlang people)
* Token bootstrapped via Ethereum
* Consensus algorithm: optimised PoW in the style of Bitcoin-NG (epochs are started by PoW *key-blocks*, which are then followed by *microblocks* including transactions, but not requiring PoW)
* The following first class objects can appear in transactions: oracles, names, tokens (represent real world objects; i.e., multi-asset), governance (protocol updates), and state channels.

### State channels

State channels are set up between two parties. Their creation and destruction (settlement) is recorded on the blockchain, but usually not any of the intermediate states. On creation both parties need to commit some funds (Æon) to the new state channel. These funds constitute the entirety of the resources that the state channel can work with.

* State changes in the channel are communicated and signed by both parties. At any time, either party is free to commit a signed state change to the main blockchain. Except in the case of a dispute, this is usually not necessary until the final state of the channel has been reached and the channel is being closed.
* In order to create a smart contract between them (using Sophia), two parties must create a state channel. The contract code usually stays only in that channel and is not made public on the main chain.
* The white paper talks about a Forth-like language called *Chalang*. However, in the *Code BEAM SF 2018* video that doesn't get mentioned anymore. The original Chalang design had the following properties:
  * Contracts for a single transaction are stateless, but can be tied together into logic spanning multiple transactions by *hashlocks*.
  * Channels state can be a new distribution of funds in the channel or a contract that computes a new distribution.
  * Limits of stateless contracts: (1) can’t implement a DAO; (2) can’t implement a subcurrency not tied to the main currency; and can’t implement a custom name system.

### Oracles

The purpose of oracles is to record real-world data on the blockchain. That data is structured and may be fairly large. Oracles in Æternity essentially consist of three different transaction types to (1) create a new oracle, (2) send a query to an oracle, and (3) for an oracle to respond to a query. This is purely an information exchange mechanism without any guarantees concerning the validity of the information supplied by the oracle (except that it does come from whoever registered the oracle in question).

Æternity provide a [more detailed description](https://github.com/aeternity/protocol/blob/master/oracles/oracles.md) of how oracles function.

## Varna

Varna is a (near) Turning complete language with statically determined execution costs (no runtime gas model). It is in spirit similar to Bitcoin Script, but comes with a functional syntax and is more expressive due to the range of first-class objects on the Æternity besides Æon. Varna is translated to code for the HLM, which is run during transaction validation by mining nodes.

## Sophia

Typed, functional language, which is essentially a variant of the ML dialect [Reason](https://reasonml.github.io).

* Translated to code of the FTWVM (Functional Typed Warded Virtual Machine):
  * Variable word length
  * Associative memory holding tagged data
  * All instructions and memory positions are typed.
  * All instructions are *warded* (i.e., checked for overflow, underflow, matching types, etc).
* Compiler performs type-preserving compilation
* Not further detailed support for specifying and proving properties
