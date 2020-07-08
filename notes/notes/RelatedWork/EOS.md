# EOS

* [Website](https://www.eos.io)
* [White paper](https://github.com/EOSIO/Documentation/blob/master/TechnicalWhitePaper.md/)
* [GitHub](https://github.com/eosio)
* Account-based ledger
* Smart contracts: generic virtual machine model based on *actions* recorded on the blockchain
* Status: as of April 2018, running a public testnet 


## The blockchain architecture

Firstly, EOS is more like a blockchain template rather than a specific blockchain. EOS tokens are ERC20 tokens on Ethereum that are used to fund the company behind EOS ([block.one](http://block.one)). They consider EOS on operating system on which scalable *Decentralised Autonomous Communities “DACs”* can be run and write a software stack (EOS.IO) that *others* can use to do so. (Block.one said explicitly that they will never run an EOS.IO blockchain themselves.)

* Proof-of-stake: [BFT-DPOS](https://steemit.com/dpos/@dantheman/dpos-consensus-algorithm-this-missing-white-paper)
* No fixed virtual machine or smart contract language


## Smart Contracts & Virtual Machines

EOS does not include its own virtual machine or contract language. Instead, they provide a message-oriented API to which they attach existing sandboxed execution environments. In particular, they provide support for [WebAssembly](https://en.wikipedia.org/wiki/WebAssembly); i.e., browser sandboxes for low-level stack-machine code. WebAssembly is a general platform with support for C, C++, and also Rust.

The blockchain'ss foremost purpose is to coordinate delivery of authenticated messages (called *actions*) to accounts. Accounts can include scripts that are triggered upon receipt of actions that they are associated with. The scripts have access to a private database associated with the account and can in turn send actions to other accounts. These scripts make up DApp's whose state DApp is fully determined by the sequence of action messages that they received since they were launched, which means it is sufficient for the chain to only record those messages.

The job of the minter nodes is to verify and combine a bunch of messages into a block and then run the DApps that receive these messages by feeding them those messages. That in turn might produce new messages from those DApps. A particular node is free to not run DApps that it is not interested in (by simply not including any message to that DApp in the blocks it mints).

The resources to run those DApps (which are arbitrary programs of which we have no a priori resource information) need to be provided by the minting nodes. However, the amount of resources that a single DApp may consume are determined by a proof-of-stake scheme. Essentially, the proportion of coins (wrt to all coins on the chain) held by the DApp owner grant them the corresponding fraction of storage space (of all storage space available to the blockchain). For compute and bandwidth resources, it is essentially the same, but in that case delegation is allowed when determining the stakes.

If a DApp tries to consume more than their allotted resources, the minting nodes are free to ignore them. But how resource usage is measured is left to the core nodes to determine by themselves. 

Example contracts in the GitHub repo are written in C++ (for use with WebAssembly).
