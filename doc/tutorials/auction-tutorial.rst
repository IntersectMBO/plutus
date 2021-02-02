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
We need some datatypes for the states and the inputs to move between them.

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

Transitions
^^^^^^^^^^^

Next we're going to define the transitions of the state machine, using the functions provided by the ``Language.Plutus.Contract.StateMachine`` module.
With this module we can build a state machine script from a transition function.
The state machine module wraps the script in some extra code that deals with the lower-level interface to the transaction.
This means that it's enough for us to define the transition function - the state machine library takes care of turning this into an actual validator.

For a state machine with state ``s`` and input ``i`` we define a transition function with this signature:

.. code-block::haskell

  transition :: State s -> i -> Maybe (TxConstraints Void Void, State s)

So we take a ``State s``, an input of type ``i`` and return a tuple of some transaction constraints and a new ``State s`` value, or ``Nothing``.

In the auction contract we use the types ``AuctionState`` for ``s`` and ``AuctionInput`` for ``i``.
But in order to tell whether a given ``AuctionInput`` is a valid transition for a current state ``AuctionState``, we need to look at the ``AuctionParams`` that define the auction (because we have to check whether the time for submitting bids has passed).
That is why whe add an additional argument to the transition function.
We also have to include the ``INLINABLE`` compiler pragma to make sure that the Plutus GHC plugin can find the definition of the transition function.

.. literalinclude:: Auction.hs
   :start-after: BLOCK3
   :end-before: BLOCK4

To define the two transitions of the state machine we look at the auction parameters, the current state (which includes both the ``AuctionState`` value and the cryptocurrency amount that is currently locked by the state machine), and the ``AuctionInput`` that was provided by the user.
Then we decide whether the transition is valid.
If it is valid we produce the new state and some constraints on the transaction that makes this state change.
If it is invalid we produce ``Nothing``.

.. literalinclude:: Auction.hs
   :start-after: BLOCK4
   :end-before: BLOCK5


The final state
^^^^^^^^^^^^^^^

The last part that is missing from our definition of the auction state machine is a function that decides whether a state is the final state.
This is an easy decision:
The ``Finished`` state is the final state and all other states are not final.
We use the ``isFinal`` function and the ``auctinTransition`` function to build a ``StateMachine``:

.. literalinclude:: Auction.hs
  :start-after: BLOCK5
  :end-before: BLOCK6

And that concludes the on-chain part of the auction state machine.
The rest of the code deals with compiling the transition function to a Plutus script, and with building and submitting the transactions that actually move the contract forward.

Compiling the state machine
^^^^^^^^^^^^^^^^^^^^^^^^^^^

Next we need some glue code to tell the compiler that we want to use the auction state machine in two ways, as a regular Haskell function and as a Plutus script.

.. literalinclude:: Auction.hs
  :start-after: BLOCK6
  :end-before: BLOCK7

These invocations of template Haskell and library functions are a bit repetitive but they ensure that we get a nice interface to the state
machine contract.

Writing the off-chain code
--------------------------

