.. highlight:: haskell
.. _english_auction_tutorial:

English auction example
==========================

Overview
------------

.. note::
    The heart of the task here is to learn how to build a script that is smart enough to say yes or no regarding whether a transaction can consume an output in a way that matches the intended behavior.

This tutorial describes the general structure, logic and code needed for designing and writing a Plutus smart contract that can be used for an English auction that is executed on the Cardano blockchain.

Key aspects of this example are the EUTXO model, the concepts involved in designing the UTXOs and EUTXOs, Plutus code examples, and the actions required of the parties involved with the auction transactions.

Specific code examples are included with detailed explanations of what the code is doing.

General requirements or recommendations for the developer environment
------------------------------------------------------------------------

*For this section, include any general information, recommendations or tips to help developers have a smooth experience.*

*I don't know if these statements below are helpful or accurate. They come from the original version of this tutorial...*

The easiest way to build Plutus currently is to use Nix. The Plutus team is working on providing a Docker image, which will help.

Plutus is built with Haskell, which can have a tough learning curve for those coming from an imperative programming background.

Plutus is new and this means that there are not necessarily as many help resources available as we would prefer. However, some of the most helpful resources to know about are:

* [A few links to helpful info/resources]
* StackOverflow posts?
* IOG Technical Community on Discord?
* Links to other IOG pages/resources?

Key concepts
----------------

EUTXO model
~~~~~~~~~~~~~~~

In order to write Plutus smart contracts, you need to understand the accounting model that Plutus and Cardano use, which is the Extended Unspent Transaction Output (EUTXO) model. This is different than the Bitcoin and Ethereum models for creating smart contracts in some critical ways. Cardano's EUTXO model has some significant advantages, but it requires a new way of thinking about smart contracts.

For a full description of the EUTXO model, please see: `The EUTXO Handbook <https://www.essentialcardano.io/article/the-eutxo-handbook>`_.

Highlights of the EUTXO model -- maybe delete this section as unnecessary and out of scope
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

UTXO, or unspent transaction outputs, are transaction outputs from previous transactions that have occurred on the blockchain and that have not yet been spent. The EUTXO model adds arbitrary logic capabilities to the transactions.

Unlike the UTXO model, which has just one condition -- that the appropriate signature is present in the transaction -- we replace this with arbitrary logic.

Instead of just having an address that corresponds to a public key that can be verified by a signature that is added to the transaction, we have more general addresses, not based on public keys or the hashes of public keys, but instead contain arbitrary logic which decides under which conditions a particular UTXO can be spent by a particular transaction.

* Redeemer
* Script Context
* Bitcoin approach
* Ethereum approach
* Cardano approach

Diagram/graphic of how the smart contract works
--------------------------------------------------

*Need to reassess what sort of diagrams would be most helpful.*

The general flow of the English auction smart contract logic
----------------------------------------------------------------

Laying the groundwork
~~~~~~~~~~~~~~~~~~~~~~~~~

.. note::
    A transaction is something that contains an arbitrary number of inputs and an arbitrary number of outputs. The effect of a transaction is to consume inputs and produce new outputs.

In this English Auction example, the item owner, Alice, wants to auction an NFT (Non-fungible token), a native token on Cardano that exists only once. An NFT can represent a piece of digital art or possibly a real-world asset.

The auction takes into account these parameters:

* the owner of the token,
* the token itself,
* a minimal bid, and
* a deadline.

The owner creates a UTXO at the script output.

The value of the UTXO is the NFT, and the datum initially is nothing. Later it will be the highest bidder and the highest bid. But at this stage, a bid has not yet taken place.

On the blockchain you can’t have a UTXO that contains only native tokens. A UTXO always has to be accompanied by some Ada, but for the sake of simplicity we will temporarily ignore that requirement for now.

Bidder transactions
~~~~~~~~~~~~~~~~~~~~~~

In this example, Bob wants to bid 100 Ada for Alice's NFT. In order to do this, Bob creates a transaction with two inputs and one output.

The two inputs are:

* the auction UTXO
* Bob's bid of 100 Ada

The output is at the output script, but now the value and the datum have changed. Previously the datum was nothing but now it has the value of: (Bob, 100).

The value has changed. Now there is not only the NFT in the UTXO, but also the 100 Ada bid.

Redeemer
~~~~~~~~~~~

As a redeemer, in order to unlock the original auction UTXO, we use something called `Bid`. This is an algebraic data type. There will be other values as well.

The auction script will check that all the conditions are satisfied. In this example, the script has to check these three conditions:

1. The bid happens before the deadline.
2. The bid is high enough.
3. The correct inputs and outputs are present (meaning that the auction is an output containing the NFT and it has the correct datum).

A second bidder
~~~~~~~~~~~~~~~~~~~~

Next, a second bidder, Charlie, wants to outbid Bob. Charlie wants to bid 200 Ada.

Charlie will create another transaction, this time one with two inputs and two outputs.
The two inputs are:

* the bid (Charlie's bid of 200 Ada)
* the auction UTXO

The two outputs are:

* the updated auction UTXO
* a UTXO that returns Bob's bid of 100 Ada

.. note::
    To clarify, technically, the auction UTXO is not getting updated because nothing ever changes. Instead,
    what really happens is that the old auction UTXO is spent and a new one is created. In a way this may feel like the auction UTXO is getting updated, but that isn't truly accurate.

Bid redeemer logic
~~~~~~~~~~~~~~~~~~~~~

This time we again use the `Bid` redeemer. The script has to check that these conditions are satisfied:

* The deadline has been reached.
* The bid is higher than the previous bid.
* The auction UTXO is correctly created.
* The previous highest bidder gets their bid back.

Transactions for closing the auction
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Finally, for this example, let’s assume that there won’t be another bid. Once the deadline has passed, the auction can be closed.

In order to do that, somebody has to create another transaction. That could be Alice who wants to collect the bid or it could be Charlie who wants to collect the NFT. It can be anybody, but Alice and Charlie have an incentive to create it.

This transaction will have one input:

* the auction UTXO, this time with the `Close` redeemer.

This transaction will have two outputs:

* One output is for the highest bidder, Charlie, who gets the NFT.
* The second output goes to Alice who gets the highest bid.

Logic
~~~~~~~~~~

In the Close case, the script checks that these conditions are satisfied:

* The deadline has been reached.
* The winner gets the NFT.
* The auction owner gets the highest bid.

When there are no bidders
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Finally, we need to consider the scenario in which nobody bids in the auction. Alice creates the auction, but the auction receives no bids. In this case, there must be a mechanism for Alice to retrieve her NFT.

To address this possibility, Alice creates a transaction with the `Close` redeemer. However, because there is no bidder, the NFT doesn’t go to the highest bidder, but instead simply goes back to Alice.

The logic in this case is slightly different. It will check that the NFT goes back to Alice. However, it doesn’t need to check the recipient because the transaction will be triggered by Alice and she can send the NFT wherever she wants.

On-chain code explanation
-----------------------------

On-chain code is the scripts we were discussing -- the scripts from the EUTXO model. In addition to public key addresses, we have a script address. Outputs can sit at such an address, and if a transaction tries to consume such an output, the script is executed. The transaction is only valid if the script succeeds.

If a node receives a new transaction, it validates it before accepting it into its mempool and eventually into a block. For each input of the transaction, if that input happens to be a script address, the corresponding script is executed. If the script does not succeed, the transaction is invalid.

Plutus Core
~~~~~~~~~~~~~~

The programming language this script is expressed in is called (Untyped) Plutus Core, but you never write Plutus Core by hand.
Instead, you write Plutus Tx (a subset of Haskell) and that gets compiled down to Plutus Core.
Eventually there may be other high-level languages such as Solidity, C or Python that can compile down to Plutus Core.

The task of a script is to say yes or no regarding whether a transaction can consume an output.

Next we'll go over the Plutus Tx code for the auction validator.
The full source code can be found in `AuctionValidator.hs <https://github.com/input-output-hk/plutus/blob/master/doc/read-the-docs-site/tutorials/AuctionValidator.hs>`_.

First, let's define the following data types and instances for the validator:

.. literalinclude:: AuctionValidator.hs
   :start-after: BLOCK1
   :end-before: BLOCK2

The purpose of ``makeLift`` and ``unstableMakeIsData`` will be explained later.

Typically, writing a Plutus validator script for a smart contract involves four data types:

* Contract parameters.
  These are properties of the contract that don't change.
  In our example, it is the ``AuctionParams`` type, containing properties like seller and minimum bid.
* Datum.
  This should be thought of as the state of the contract.
  Our example requires only one piece of state: the current highest bid, which we use the ``AuctionDatum`` type to represent.
* Redeemer.
  This is the input to the contract that generates a new state.
  In our example it is the ``AuctionRedeemer`` type: one may either submit a new bid, or request to close the auction and pay out the winner and the seller.
* Script context.
  This type contains the information of the transaction that the validator can inspect.
  In our example, our validator verifies several conditions of the transaction, e.g., if it is a new bid, then it must be submitted before the auction's end time, and the previous highest bid must be refunded to the previous bidder.

  The script context type is fixed for each language version, e.g., for Plutus V2, it is ``PlutusLedgerApi.V2.Contexts.ScriptContext``.

One thing worth mentioning here is that when writing a Plutus validator using Plutus Tx, it is advisable to turn off Haskell's ``Prelude``.
Usage of most functions and methods in ``Prelude`` should be replaced by their counterparts in the ``PlutusTx`` library, e.g., ``PlutusTx.==``.

Now we are ready to introduce our main validator function.
The beginning of the function looks like the following:

.. literalinclude:: AuctionValidator.hs
   :start-after: BLOCK2
   :end-before: BLOCK3

Depending on whether this transaction is attempting to submit a new bid or request payout, the validator validates the corresponding set of conditions.

The ``sufficientBid`` contidion verifies that the bid amount is sufficient:

.. literalinclude:: AuctionValidator.hs
   :start-after: BLOCK3
   :end-before: BLOCK4

The ``validBidTime`` condition verifies that the bid is submitted before the auction's end time:

.. literalinclude:: AuctionValidator.hs
   :start-after: BLOCK4
   :end-before: BLOCK5

Here, ``to x`` is the time interval ending at ``x``, i.e., ``(-∞, x]``.
``txInfoValidRange`` is a transaction property.
It is the time interval in which the transaction is validated.
``contains`` takes two time intervals, and checks that the first interval completely includes the second.
Since the transaction may be validated at any point in the ``txInfoValidRange`` interval, we need to check that the entire interval lies within ``(-∞, apEndTime params]``.

The reason we need the ``txInfoValidRange`` interval, instead of using the exact time the transaction is validated, is `determinism <https://iohk.io/en/blog/posts/2021/09/06/no-surprises-transaction-validation-on-cardano/>`_.
A transaction validated off-chain must not fail at phase 2 on-chain.
If we use the exact time, then we cannot guarantee this, because the exact time is different when validating the script off-chain vs. on-chain.
On the other hand, by using the ``txInfoValidRange`` interval, the same interval is used both off-chain and on-chain, and as a result, only phase 1 validation failures are possible, not phase 2.

The ``refundsPreviousHighestBid`` condition checks that the transaction pays the previous highest bid to the previous bidder:

.. literalinclude:: AuctionValidator.hs
   :start-after: BLOCK5
   :end-before: BLOCK6

It uses ``PlutusTx.filter`` to find the transaction output (a UTXO) that pays to the previous bidder the amount equivalent to the previous highest bid, and verifies that there is exactly one such output.

``singleton adaSymbol adaToken amt`` constructs a ``Value`` with ``amt`` Lovelaces.
``Value`` is a multi-asset type that represents a collection of assets, including Ada.
An asset is identified by a (symbol, token) pair, where the symbol represents the policy that controls the minting and burning of tokens, and the token represents a particular kind of token manipulated by the policy.
``(adaSymbol, adaToken)`` is a special identifier for Ada/Lovelace.

The ``correctNewDatum`` condition verifies that the transaction produces a *continuing output* containing the correct datum (the new highest bid):

.. literalinclude:: AuctionValidator.hs
   :start-after: BLOCK6
   :end-before: BLOCK7

A "continuing output" is a transaction output that pays to the same script address we are currently spending from.
Exactly one continuing output must be present in this example, so that the next bidder can place a new bid, which will need to spend the continuing output and get validated by the same validator script.

If the transaction is requesting a payout, the validator will then verify the other three conditions: `validPayoutTime`, `sellerGetsHighestBid` and `highestBidderGetsAsset`. These conditions are similar to the ones already explained, so their details are omitted.

Finally, we need to compile the validator written in Plutus Tx into Untyped Plutus Core (UPLC), using the Plutus Tx compiler:

.. literalinclude:: AuctionValidator.hs
   :start-after: BLOCK8
   :end-before: BLOCK9

The type of the compiled validator is ``CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())``, where type ``BuiltinData -> BuiltinData -> BuiltinData -> ()`` is also known as the *untyped validator*.
An untyped validator takes three ``BuiltinData`` arguments, representing the serialized datum, redeemer, and script context. The call to ``PlutusTx.unsafeFromBuiltinData`` is the reason we need the ``PlutusTx.unstableMakeIsData`` shown before, which derives ``UnsafeFromData`` instances. And instead of returning a ``Bool``, it simply returns ``()``, and the validation succeeds if the script evaluates without error.

Note that ``AuctionParams`` is not an argument of either the untyped validator, or the final UPLC program. As said before, it contains contract properties that don't change, and so it is simply built into the validator.

Since the PlutusTx compiler compiles ``a`` into ``CompiledCode a``, we first use ``auctionUntypedValidator`` to obain an untyped validator. It takes ``AuctionParams``, and returns an untyped validator.
We then define the ``auctionValidatorScript`` function, which takes ``AuctionParams`` and returns the compiled UPLC program.

It is worth noting that we must call ``PlutusTx.compile`` on the entire ``auctionUntypedValidator``, rather than applying it to ``params`` before compiling, as in ``$$(PlutusTx.compile [||auctionUntypedValidator params||])``.
The latter won't work, because everything being compiled (inside ``[||...||]``) must be known at compile time, but ``params`` is not: it is a formal parameter.
So instead, we compile the entire ``auctionUntypedValidator`` into UPLC, then use ``liftCode`` to lift ``params`` into a UPLC term, and apply the compiled ``auctionUntypedValidator`` to it at the UPLC level. To do so, we need the ``Lift`` instance for ``AuctionParams``, derived via ``PlutusTx.makeLift``.

Now, to create the Plutus validator script for a particular auction, we simply call ``auctionValidatorScript`` with the appropriate ``AuctionParams``.
We will then be able to launch the auction on-chain by submitting a transaction that locks the asset being auctioned at the script address with ``AuctionDatum Nothing`` as the datum.

Libraries for Writing Plutus Tx Scripts
~~~~~~~~~~~~~~~~

This auction example shows a relatively low-level way of writing scripts using Plutus Tx.
In practice, you may consider using a higher level library that abstracts away some of the details.
For example, `plutus-apps <https://github.com/input-output-hk/plutus-apps>`_ provides a state machine library and a constraint library for writing Plutus Tx.
Using these libraries, writing a validator in Plutus Tx becomes a matter of defining state transactions and the corresponding constraints, e.g., the condition ``refundsPreviousHighestBid`` can simply be written as ``Constraints.mustPayToPubKey bidder (singleton adaSymbol adaToken amt)``.

Off-chain Code
----------------------------------------------------

Since the main purpose of this page is to introduce Plutus Tx and Plutus Core, we only walked through the on-chain code, responsible for validating transactions (in the sense of determining whether a transaction is allowed to spend a UTXO).

In addition to the on-chain code, one typically needs the accompanying off-chain code and services to perform tasks like building transactions, submitting transactions, deploying smart contracts, querying for available UTXOs on the chain, etc.
A full suite of solutions is provided in the Plutus Application Framework.
See the `plutus-apps <https://github.com/input-output-hk/plutus-apps>`_ repo and its `Read the Docs site <https://plutus-apps.readthedocs.io/en/latest/>`_ for more details.
