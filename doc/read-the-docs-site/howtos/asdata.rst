.. highlight:: haskell
.. _asdata:

How to use ``AsData`` to optimize scripts
=========================================

The latest Plutus libraries contain a new ``PlutusTx.asData`` module that contains Template Haskell (TH) code for encoding algebraic data types (ADTs) as ``Data`` objects in Plutus Core, as opposed to sums-of-products terms.
In general, ``asData`` pushes the burden of a computation nearer to where a value is used, in a crude sense making the evaluation less strict and more lazy.
This is intended for expert Plutus developers.

Purpose
-------

When writing and optimizing a Plutus script, one of the challenges is finding the right balance for your specific use case between which method to use for handling ``Data`` objects and how expensive that method will be.
To make an informed decision, you may need to benchmark and profile your smart contract code to measure its actual resource consumption.
The primary purpose of ``asData`` is to give you more options for how you want to handle ``Data``.

Choice of two pathways
----------------------

When handling ``Data`` objects, you have a choice of two pathways.
It is up to you to determine which pathway to use depending on your particular use case.
There are trade offs in performance and where errors occur.

Method one: proactively do all of the parsing
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The first approach is to parse the object immediately (using ``fromBuiltinData``) into a native Plutus Core datatype, which will also identify any problems with the structuring of the object.
However, this performs all the work up front.

Method two: only do the parsing if and when necessary
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

In the second approach, the validator doesn't necessarily do anything. It only does the work when it needs to. In order to work with the data objects, the validator has to call the builtin functions, which is a little bit more expensive. It might be that this saves you a lot of work, because you may never need to parse the entire object. Instead, the validator will just carry the item around as if it were a data object. Some time later, when the validator needs to do an operation with this integer, then the validator will parse it. If it determines that it is not an integer, there will be errors.
Using this method, every time the validator parses it, it is going to look at the data object to find out if it is an integer. If it is an integer, it will get the integer out and do its processing. The analysis work may be repeated depending on how your script is written. In some cases, you might do less work, in some cases you might do more work, depending on your specific use case.

Using ``asData``
------------------
``asData`` works best when you use it for a type and all the types that go into it. The ``asData`` function takes the definition of a data type and replaces it with an equivalent definition whose representation uses ``Data`` directly.

``Data`` objects versus Plutus Tx's datatypes
---------------------------------------------
There are tradeoffs relating to the slower processing speed of ``Data`` objects versus Plutus Tx's datatypes.

Values stored in datums or redeemers
------------------------------------


Values stored in datums or redeemers need to be encoded into ``Data`` objects.
This means that when a script starts to work with its datum or redeemer, it often wants to parse it into a more structured format using Plutus Tx's support for datatypes.
Usually this is done with the ``fromBuiltinData`` function.

The problem is that ``fromBuiltinData`` has to traverse the entire ``Data`` object in order to perform the transformation, which is costly.
The alternative is to work directly with the raw ``Data`` object.

These two approaches have tradeoffs:

1. If the resulting object is going to be processed in its entirety, or have parts of it repeatedly processed, then it can be better to convert it, since Plutus Tx's datatypes are faster to work with than ``Data``.
2. If it is important to check that the entire structure is well-formed, then it is better to convert it, since the conversion will check for well-formedness.
3. If correctness is important, then it can be better to convert it, since the compiler can help you more if you are using Plutus Tx's datatypes.

Generally, which approach is better is an empirical question and may vary in different cases.
Often the cost of ``fromBuiltinData`` can be very significant and so it is desirable to use a ``Data`` representation, but the third point above can be quite painful.

The ``plutus-tx`` library provides a tool to make it possible to use a raw ``Data`` representation while still getting the same amount of help from the compiler.
The ``asData`` function takes the definition of a data type and replaces it with an equivalent definition whose representation uses ``Data`` directly.

For example, if we wanted to use it on the types from the :ref:`auction example<simple_example>`, we would put the datatype declarations inside a Template Haskell quote and call ``asData`` on it.

.. literalinclude:: ../tutorials/AuctionValidator.hs
   :start-after: BLOCK9
   :end-before: BLOCK10

This is normal Template Haskell that just generates new Haskell source, so you can see the code that it generates with `{-# OPTIONS_GHC -ddump-splices #-}`, but it will look something like this:

.. code-block::

        PlutusTx.asData
        [d| data Bid'
                = Bid' {bBidder' :: PubKeyHash, bAmount' :: Lovelace}
                deriving newtype (Eq, Ord, ToBuitinData, FromBuiltinData, UnsafeFromBuiltinData)
            data AuctionRedeemer' = NewBid' Bid | Payout'
                deriving newtype (Eq, Ord, ToBuitinData, FromBuiltinData, UnsafeFromBuiltinData) |]

        ======>

        newtype Bid' = Bid'2 BuiltinData
        deriving newtype (Eq, Ord, PlutusTx.ToData, FromData, UnsafeFromData)

        {-# COMPLETE Bid' #-}
        pattern Bid' :: PubKeyHash -> Lovelace -> Bid'
        pattern Bid' ...

        newtype AuctionRedeemer' = AuctionRedeemer'2 BuiltinData
        deriving newtype (Eq, Ord, PlutusTx.ToData, FromData, UnsafeFromData)

        {-# COMPLETE NewBid', Payout' #-}
        pattern NewBid' :: Bid -> AuctionRedeemer'
        pattern NewBid' ...
        pattern Payout' :: AuctionRedeemer'
        pattern Payout' ...

That is:

- It creates a newtype wrapper around ``BuiltinData``
- It creates pattern synonyms corresponding to each of the constructors you wrote

This lets you write code "as if" you were using the original declaration that you wrote, while in fact the pattern synonyms are handling conversion to/from ``Data`` for you.
But any values of this type actually are represented with ``Data``.
That means that when we newtype-derive the instances for converting to and from ``Data`` we get the instances for ``BuiltinData`` - which are free!

Caveats
-------

The most important caveat to using ``asData`` is that ``Data`` objects encoding datatypes must also encode the *fields* ``Data``.
However, when using the pattern synonyms they try to give you exactly what you asked for, which might mean having the fields *not* encoded as ``Data``.

For example, in the ``Bid`` case above the ``Lovelace`` field is represented as a Plutus Core builtin integer.
However, in order for it to be encoded into the ``Bid`` structure, we need to encode it into ``Data``.
That means that when you construct a ``Bid`` object you do an ``Integer`` to ``Data`` conversion, and when you pattern match on a ``Bid`` object you do a ``Data`` to ``Integer`` conversion.

These conversions are potentially expensive!
Whether or not this is a problem depends on the precise situation, but in general:

- If the field is a builtin integer or bytestring or a wrapper around those, it is probably cheap
- If the field is a datatype which is itself defined with ``asData`` then it is free (since it's already ``Data``!)
- If the field is a complex or large datatype then it is potentially expensive

Therefore ``asData`` tends to work best when you use it for a type and all the types that go into it.

Finally, you should bear in mind the tradeoffs mentioned at the start of this article relating to the slower processing speed of ``Data`` objects versus Plutus Tx's datatypes.
