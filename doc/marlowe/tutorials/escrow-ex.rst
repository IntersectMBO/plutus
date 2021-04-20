.. _escrow-ex:

A first example
===============

This tutorial introduces a simple financial contract in pseudocode,
before explaining how it is modified to work in Marlowe, giving the
first example of a Marlowe contract.

A simple escrow contract
------------------------

.. image:: images/escrow.png
   :alt: Escrow

Suppose that ``alice`` wants to buy a cat from ``bob``, but neither of
them trusts the other. Fortunately, they have a mutual friend ``carol``
whom they both trust to be neutral (but not enough to give her the money
and act as an intermediary). They therefore agree on the following
contract, written using simple functional pseudocode. This kind of
contract is a simple example of *escrow*.

.. code:: haskell

   When aliceChoice
        (When bobChoice
              (If (aliceChosen `ValueEQ` bobChosen)
                  agreement
                  arbitrate))

The contract is described using the *constructors* of a Haskell data
type. The outermost constructor ``When`` has two arguments: the first is
an *observation* and the second is another contract. The intended
meaning of this is that *when* the action happens, the second contract
is activated.

The second contract is itself another ``When`` – asking for a decision
from ``bob`` – but inside that, there is a *choice*: ``If`` ``alice``
and ``bob`` agree on what to do, it is done; if not, ``carol`` is asked
to arbitrate and make a decision.

In general ``When`` offers a *list of cases*, [1]_ each with an action
and a corresponding contract that is triggered when that action happens.
Using this we can allow for the option of ``bob`` making the first
choice, rather than ``alice``, like this:

.. code:: haskell

     When [ Case aliceChoice
                 (When [ Case bobChoice
                             (If (aliceChosen `ValueEQ` bobChosen)
                                agreement
                                arbitrate) ],
           Case bobChoice
                 (When [ Case aliceChoice
                             (If (aliceChosen `ValueEQ` bobChosen)
                                 agreement
                                 arbitrate) ]
          ]

In this contract, either Alice or Bob can make the first choice; the
other then makes a choice. If they agree, then that is done; if not,
Carol arbitrates. In the remainder of the tutorial we’ll revert to the
simpler version where ``alice`` chooses first.

   **Exercise**

   Think about executing this contract in practice. Suppose that Alice
   has already committed some money to the contract. What will happen if
   Bob chooses not to participate any further?

   We have assumed that Alice has already committed her payment, but
   suppose that we want to design a contract to ensure that: what would
   we need to do to?

Escrow in Marlowe
-----------------

Marlowe contracts incorporate extra constructs to ensure that they
progress properly. Each time we see a ``When``, we need to provide two
additional things:

-  a *timeout* after which the contract will progress, and

-  the *continuation* contract to which it progresses.

Adding timeouts
---------------

First, let us examine how to modify what we have written to take care of
the case that the condition of the ``When`` never becomes true. So, we
add timeout and continuation values to each ``When`` occurring in the
contract.

.. code:: haskell

     When [ Case aliceChoice
                 (When [ Case bobChoice
                             (If (aliceChosen `ValueEQ` bobChosen)
                                agreement
                                arbitrate) ]
                       60            -- ADDED
                       arbitrate)    -- ADDED
           ]
           40           -- ADDED
           Close        -- ADDED

The outermost ``When`` calls for the first choice to be made by Alice:
if Alice has not made a choice by slot ``40``, the contract is closed
and all the funds in the contract are refunded.

``Close`` is typically the last step in every “path” through a Marlowe
contract, and its effect is to refund the money in the contract to the
participants; we will describe this in more detail when we look at
:ref:`Marlowe step by step <marlowe-step-by-step>`
in a later tutorial. In this particular case, refund will happen at slot
number ``40``.

Looking at the inner constructs, if Alice’s choice has been made, then
we wait for one from Bob. If that is not forthcoming by slot ``60``,
then Carol is called upon to arbitrate. [2]_

Adding commitments
------------------

Next, we should look at how *cash is committed* as the first step of the
contract.

.. code:: haskell

    When [Case (Deposit "alice" "alice" ada price)   -- ADDED
     (When [ Case aliceChoice
                 (When [ Case bobChoice
                             (If (aliceChosen `ValueEQ` bobChosen)
                                agreement
                                arbitrate) ]
                       60
                       arbitrate)
           ]
           40
           Close)
       ]
       10                                      -- ADDED
       Close                                   -- ADDED

A deposit of ``price`` is requested from ``"alice"``: if it is given,
then it is held in an account, also called ``"alice"``. Accounts like
this exist for the life of the contract only; each account belongs to a
single contract.

There is a timeout at slot number ``10`` on making the deposit; if that
is reached without a deposit being made, the contract is closed and all
the money already in the contract is refunded. In this case, that is
simply the end of the contract.

Definitions
-----------

We will see :ref:`later <embedded-marlowe>` that parts
of this contract description, such as ``arbitrate``, ``agreement``, and
``price``, use the Haskell *embedding* of Marlowe DSL to give some
shorthand definitions. We also use *overloaded* strings to make some
descriptions – e.g. of accounts – more concise.

These are discussed in more detail when we look at :ref:`Marlowe embedded in
Haskell <embedded-marlowe>`.

   **Exercise**

   Comment on the choice of timeout values, and look at alternatives.

   For example, what would happen if the timeout of ``40`` on the
   ``When`` were to be replaced by ``60``, and vice versa? Would it be
   sensible to have the same timeout, of ``100`` say, on each ``When``?
   If not, why not?

This example has shown many of the ingredients of the Marlowe contract
language; in the next tutorial we will present the complete language.

Notes
-----

-  While accounts names need to be provided manually in the example
   here, these could be generated by users’ wallets in a version of
   Marlowe deployed on a blockchain.

Where to go to find out more
----------------------------

These papers cover the original work on using functional programming to
describe financial contracts.

-  `Composing contracts: an adventure in financial
   engineering <https://www.microsoft.com/en-us/research/publication/composing-contracts-an-adventure-in-financial-engineering/>`_

-  `Certified symbolic management of financial multi-party
   contracts <https://dl.acm.org/citation.cfm?id=2784747>`_

.. [1]
   Lists in Marlowe are included in square brackets, as in ``[2,3,4]``.

.. [2]
   Again, we will describe how ``arbitrate`` and ``agreement`` work in
   :ref:`embedded Marlowe <embedded-marlowe>`.
