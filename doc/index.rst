The Plutus Platform
===================

The Plutus Platform is the smart contract platform of the Cardano blockchain.
Plutus contracts consist of pieces that run on the blockchain (*on-chain* code) and pieces that run on a user’s machine (*off-chain* or *client* code).

Both on-chain and off-chain code is written in Haskell, and Plutus smart contracts are Haskell programs.
Off-chain code is compiled by GHC, the Haskell compiler, and on-chain code is compiled by the Plutus compiler.

Smart contracts
---------------

From the smart contract author’s perspective, the blockchain is a distributed bookkeeping system.
It keeps track of who owns how much of a virtual resource (Bitcoin, Ada, etc.) and records when assets are transferred from one entity to another.
The owners of digital assets are identified by their public keys, and they may be people or machines.

Smart contracts are programs that control the transfer of resources on the blockchain.
When two parties decide to enter a smart contract, they place some of their own assets under the control of an on-chain program which enforces the rules of the contract.
Every time someone wants to take assets out of the contract, the program is run, and only if its output is positive are the assets released.

On the Cardano blockchain, the on-chain programs are written in a language called *Plutus Core*.
However, smart contract authors do not write Plutus Core directly.
The Plutus Platform is a software development kit which enables smart contract authors to easily write smart contracts, including the logic that will eventually be run on the blockchain as Plutus Core.

To write a smart contract using the Plutus Platform, you can code directly in the Plutus Playground.
The Plutus Playground is a lightweight, web-based environment for exploratory Plutus development. Here you can easily write and simulate deployment of your contracts without the overhead of installing and maintaining a full development environment.

You can also use a normal Haskell development environment on your computer to write Plutus programs. See the main `Plutus repository <https://github.com/input-output-hk/plutus>`_ for more information.

.. toctree::
   :caption: Explore Plutus
   :maxdepth: 2

   tutorials/index

.. toctree::
   :caption: Plutus Reference
   :maxdepth: 2

   reference/index

References
----------

1. Haskell_ is the programming language for Plutus contracts. 
2. We also generate the developer documentation from our source code using Haddock_. You can also find this documentation in the Playground.
3. If you want to talk to us directly, you can use the Cardano Forum_.

.. _Haskell: http://haskell.org/
.. _Haddock: https://www.haskell.org/haddock/index.html
.. _Forum: http://forum.cardano.org/

