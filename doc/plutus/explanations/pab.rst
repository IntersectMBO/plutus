.. _what_is_the_pab:

What is the PAB?
================

PAB is short for *Plutus Application Backend*.
The Plutus Application Backend is the client-side runtime for :term:`Plutus apps<contract application>` that are built with the :ref:`Plutus Platform<what_is_the_plutus_platform>`.
It is the PAB's task to deal with requests from running ``Contract`` instances, to forward user input to them, and to notify them of ledger state change events.

.. TODO: Ref. to `Contract` type

The ``plutus-pab`` cabal package in the Plutus repository defines a ``plutus-pab`` Haskell library.
Application developers use this library to build the actual PAB executable, specialised to one or more of their ``Contract`` s.

Client interface
----------------

The PAB provides an HTTP and websocket interface for interacting with ``Contract`` instances.
All PAB operations, including starting new instances, calling endpoints on instances, and querying instance state, are performed using this API.
Application developers can build their own frontends and server processes that make HTTP calls to the PAB.

Other components
----------------

In addition to the PAB itself, the following components are required.

.. _pab_chain_index:

:ref:`Chain index<what_is_the_chain_index>`
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The PAB gets information about the ledger state and about the inverse of hash values from the chain index.

Alonzo node
~~~~~~~~~~~

The PAB subscribes to ledger state updates from the node, using a socket protocol.

Wallet
~~~~~~

A Cardano wallet is required for balancing and signing transactions.
Balancing means taking a partial transaction and adding inputs and outputs to make the transaction valid.

Take :ref:`Marlowe<introducing-marlowe>` as an example.
When the user first starts a Marlowe contract, funds need to be transferred from one of the user's addresses to the contract address.
This is achieved by sending a partial transaction that has zero inputs and a script output for the Marlowe contract instance to the wallet for balancing.
The wallet adds some of its own inputs to cover the amount that is to be paid into the contract, plus a change output for any excess funds.
When the Marlowe contract has finished, funds are transferred back to the user's wallet using the same mechanism:
The PAB sends another partial transaction, this time with a single script input and no outputs.
The wallet then adds an output at one of its own addresses to receive the funds.

Deployment Scenarios
--------------------

There are two deployment models envisaged for the PAB: Hosted and in-browser.
The hosted variant will be supported at the initial release of the PAB.
The in-browser variant wil be available after the initial release.

Hosted
~~~~~~

In the “Hosted PAB” scenario, the dApp provider / developer hosts an instance of the PAB alongside the :ref:`chain index<pab_chain_index>` and an Alonzo node.
The off-chain code of the Plutus app is run on the dApp provider’s infrastructure.

.. figure:: ./hosted-pab.png

    The hosted deployment scenario for the PAB.

Coin selection and transaction signing (in short: anything that deals with the user’s money) happens on the user’s machine.
The PAB produces a link (URI) for each partial transaction that needs to be balanced and signed.
When the user clicks the link, the user's operating system opens the wallet that is registered to handle the link schema.
This scheme is not restricted to Daedalus, or even to full wallets.
Any wallet that implements a handler for the link schema can be used to balance, sign and submit Plutus transactions.
