.. highlight:: haskell
.. _auction_tutorial:

Writing an auction contract
===========================

In this tutorial we're going to write an auction contract.
In the auction contract, a native asset is put up for sale, and there is a time window during which participants can bid on the asset.
At the end of the time window the asset can be claimed by the highest bidder.

Contract parameters
-------------------

Each instance of the auction contract has some parameters that define it.
These parameters include the owner of the asset, the time window of the auction, and the asset itself.

.. literalinclude:: Auction.hs
  :start-after: BLOCK1
  :end-before: BLOCK2

The auction state machine
-------------------------

We're going to use the state machine library to implement the auction.
We need some datatypes for the states and the transitions between them.

.. literalinclude:: Auction.hs
   :start-after: BLOCK2
   :end-before: BLOCK3

We have two states and two possible transitions.
The ``Bid`` transition goes from the ``Ongoing`` state to the ``Ongoing`` state, and the ``Payout`` transition goes from the ``Ongoing`` to the ``Finished`` state.

Note that we use ``Ada`` for the bids and ``Value`` for the asset (in ``AuctionParams``).
Why not accept any ``Value`` for the bids?
When a new bid is submitted we need to compare it to the old bid and establish which of the two is worth more.
Only if the new bid is worth more than the old bid can we accept the new bid.

The ``Value`` type only has a partial ordering. Two ``Values`` could have to completely different currencies, or combinations of them, and it's impossible to tell which one is worth more without considering additional information such as an exchange rate.

The ``Ada`` type on the other hand has a total ordering.
It is in effect just a synonym for the integers, so we can always tell which of two ``Ada`` amounts is larger.
That is why we use ``Value`` for the asset and ``Ada`` for the price of the asset.
We could of course choose a different currency for the price.
In that case we'd have to include the currency's MPS hash and token name in the ``AuctionParams``.

TODO

* Value in AuctionParams vs Ada in AuctionState
* Slot (time)