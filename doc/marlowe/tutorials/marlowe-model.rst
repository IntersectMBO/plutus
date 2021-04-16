.. _marlowe-model:

The Marlowe model
=================

Marlowe is designed to support the execution of financial contracts on
blockchain, and specifically to work on Cardano. Contracts are built by
putting together a small number of constructs that can be combined to
describe many different kinds of financial contract.

Before we describe those constructs, we need to look at our general
approach to modelling contracts in Marlowe, and the context in which
Marlowe contracts are executed, the Cardano blockchain. In doing this we
also introduce some of the terminology that we will use, indicating
definitions by *italics*.

Contracts
---------

Contracts in Marlowe run on a blockchain, but need to interact with the
off-chain world. The *parties* to the contract, whom we also call the
*participants*, can engage in various *actions*: they can be asked to
*deposit money*, or to *make a choice* between various alternatives. A
*notification* of an external value (also called an *oracle* value),
such as the current price of a particular commodity, is the other
possible form of input. [1]_

Running a contract will also produce external *effects*, by making
payments to parties in the contract.

Participants and roles
~~~~~~~~~~~~~~~~~~~~~~

We should separate the notions of *participants* and *roles* in a
Marlowe contract. The roles in a contract are fixed and immutable, and
could be named ``party``, ``counterparty`` etc. On the other hand, the
participants that are bound to the contract roles can change during the
execution of the particular *contract instance*. This allows roles in
running contracts to be *traded* between participants, through a
mechanism of *tokenisation*. This will be available in the on-chain
implementation of Marlowe, and in the wallet-style simulation, but the
omniscient simulation simply presents contract roles.

Accounts
~~~~~~~~

The Marlowe model allows for a contract to store assets. All parties
that participate in the contract implicitly own an account with their
name. All assets stored in the contract must be in the account of one of
the parties, this way, when the contract is closed, all assets that
remain in the contract are refunded to the respective owners. These
accounts are local, in that they only exist during the execution of the
contract, and during that time they are only accessible by parties to
the contract.

Steps and states
~~~~~~~~~~~~~~~~

Marlowe contracts describe a series of *steps*, typically by describing
the first step, together with another (sub-) contract that describes
what to do next. For example, the contract ``Pay a p t v cont`` says
“make a payment of value ``v`` of token ``t`` to the party ``p`` from
the account ``a``, and then follow the contract ``cont``\ ”. We call
``cont`` the *continuation* of the contract.

In executing a contract we need to keep track of the *current contract*:
after making a step in the example above, the current contract is the
continuation, ``cont``. We also have to keep track of some other
information, such as how much is held in each account: we call this
information the state: this potentially changes at each step too. A step
can also see an action taking place, such as money being deposited, or
an *effect* being produced, e.g. a payment.

Blockchain
----------

While Marlowe is designed to work with blockchains in general, [2]_ some
details of how it interacts with the blockchain are relevant when
describing the semantics and implementation of Marlowe.

A UTxO-based blockchain is a chain of *blocks*, each of which contains a
collection of transactions. Each *transaction* has a set of inputs and
outputs, and the blockchain is built by linking *unspent transaction
outputs* (UTxO) to the inputs of a new transaction. At most one block
can be generated in each *slot*, which are 1 second long.

The mechanisms by which these blocks are generated, and by whom, are not
relevant here, but contracts will be expressed in terms of *slot
numbers*, counting from the starting (“genesis”) block of the
blockchain.

UTxO and wallets
~~~~~~~~~~~~~~~~

Value on the blockchain resides in the UTxO, which are protected
cryptographically by a private key held by the owner. These keys can be
used to *redeem* the output, and so to use them as inputs to new
transactions, which can be seen as spending the value in the inputs.
Users typically keep track of their private keys, and the values
attached to them, in a cryptographically-secure *wallet*.

It is through their wallets that users are able to interact with smart
contracts - including Marlowe contracts – running on the blockchain.
Deposits are made from users’ wallets, and payments received by them.
Note, however, that these are definitely *off chain* actions that need
to be controlled by code running in the user’s wallet: they cannot be
made to happen by the Marlowe contract itself.

Omniscient and wallet-level simulation
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The Marlowe Playground supports two kinds of simulation: the standard
*omniscient* simulation and a proof of concept *wallet-level*
simulation.

In an *omniscient* simulation, the user is able to perform any action
for any role, and thus can observe the execution from the perspective of
all the users. The *“wallet”-style* simulation explicitly models
different wallets (i.e. different participants) and their participation
in multiple roles in multiple contracts. This model thus presents a more
faithful perspective of contract execution for a particular participant
in the contract.

Value
~~~~~

In previous examples, whenever a ``Value`` was required, we have
exclusively used Ada. This makes a lot of sense, seeing as Ada is the
fundamental currency supported by Cardano.

Marlowe offers a more general concept of *value*, though, supporting
custom fungible, non-fungible, and mixed tokens.  [3]_ What *is* a
``Value`` in Marlowe?

.. code:: haskell

   newtype Value = Value
       {getValue :: Map CurrencySymbol (Map TokenName Integer)}

The types ``CurrencySymbol`` and ``TokenName`` are both simple wrappers
around ``ByteString``.

This notion of *value* encompasses Ada, fungible tokens (think
currencies), non-fungible tokens (a custom token that is not
interchangeable with other tokens), and more exotic mixed cases:

-  Ada has the *empty bytestring* as ``CurrencySymbol`` and
   ``TokenName``.

-  A *fungible* token is represented by a ``CurrencySymbol`` for which
   there is exactly one ``TokenName`` which can have an arbitrary
   non-negative integer quantity (of which Ada is a special case).

-  A class of *non-fungible* tokens is a ``CurrencySymbol`` with several
   ``TokenName``\ s, each of which has a quantity of one. Each of these
   names corresponds to one unique non-fungible token.

-  Mixed tokens are those with several ``TokenName``\ s *and* quantities
   greater than one.

Cardano provides a simple way to introduce a new currency by *forging*
it using *monetary policy scripts*. This effectively embeds Ethereum
ERC-20/ERC-721 standards as primitive values in Cardano. We use custom
tokens to represents participants in Marlowe contracts executing on
chain.

Executing a Marlowe contract
----------------------------

Executing a Marlowe contract on Cardano blockchain means constraining
user-generated transactions according to the contract’s logic. If a
contract expects a deposit of 100 Ada from Alice, only such a
transaction will succeed, anything else will be rejected.

A transaction contains an ordered list of *inputs* or *actions*. The
Marlowe interpreter is executed during transaction validation. First, it
evaluates the contract *step by step* until it cannot be changed any
further without processing any input, a condition that we call being
*quiescent*. At this stage we progress through ``When`` with passed
timeouts, ``If``, ``Let``, ``Pay``, and ``Close`` constructs without
consuming any *inputs*.

The first input is then processed, and then the contract is single
stepped again until quiescence, and this process is repeated until all
the inputs are processed. At each step the current contact and the state
will change, some input may be processed, and payments made.

Such a *transaction*, as shown in the diagram below, is added to the
blockchain. What we do next is to describe in detail what Marlowe
contracts look like, and how they are evaluated step by step.

We have shown, [4]_ that the behaviour of a Marlowe is independent of
how inputs are collected into transactions, and so when we simulate the
action of a contract we don’t need to group inputs into transactions
explicitly. For concreteness we can think of each transaction having at
most one input. While the semantics of a contract is independent of how
inputs are grouped into transactions, the *costs of execution* may be
lower if multiple inputs can be grouped into a single transaction.

In the *omniscient* simulation available in the Marlowe playground we
abstract away from transaction grouping, while in the role-based
“wallet“ simulation transactions are explicit.

.. container:: formalpara-title

   **Building a transaction**

.. image:: images/transaction.svg
   :alt: transaction

.. [1]
   We can think of oracles as another kind of party to the contract;
   under this view notifications become the choices made by that party.

.. [2]
   Indeed, Marlowe could be modified to run off blockchain, or to work
   on a permissioned blockchain, too.

.. [3]
   This reflects the value model for Plutus.

.. [4]
   In our paper `Marlowe: implementing and analysing financial contracts
   on
   blockchain <https://iohk.io/en/research/library/papers/marloweimplementing-and-analysing-financial-contracts-on-blockchain/>`_
