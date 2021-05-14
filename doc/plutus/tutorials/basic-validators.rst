.. highlight:: haskell
.. _basic_validators_tutorial:

Writing basic validator scripts
===============================

:term:`Validator scripts<validator script>` are the programs that can be used to lock transaction outputs on the chain.
Validator scripts are :term:`Plutus Core` programs, but we can use :term:`Plutus Tx` to write them easily in Haskell.

Validator arguments
-------------------

Validators receive some information from the validating node:

- The :term:`redeemer`, which is some script-specific data specified by the party spending the output.
- The :term:`datum`, which is some script-specific data specified by the party who created the output.
- The :term:`validation context`, which contains a representation of the spending transaction, as well as the index of the input whose validator is currently being run.

The validator is a function which receives these three inputs as *arguments*.
The validating node is responsible for passing them in and running the validator.

The ``Data`` type
-----------------

But how are the validator's arguments passed?
At least the redeemer and datum can be of different types depending on the script.

The answer is that we pass them as a generic structured data type :hsobj:`PlutusTx.Data.Data`.
``Data`` is designed to make it easy to encode structured data into it, and to be itself encoded as CBOR.

Consequently, the validator scripts we will write in this tutorial take three arguments of type ``Data``.

However, you will typically not want to use ``Data`` directly in your program, rather you will want to use your own datatypes.
We can easily convert to and from ``Data`` with the :hsobj:`PlutusTx.IsData.Class.IsData` typeclass.

You usually don't need to write your own ``IsData`` instances.
Instead, you can use the ``makeIsData`` Template Haskell function to generate one.

.. literalinclude:: BasicValidators.hs
   :start-after: BLOCK1
   :end-before: BLOCK2

Signaling failure
-----------------

The most important thing that a validator can do is *fail*.
This indicates that the attempt to spend the output is invalid and that transaction validation should fail.
A validator succeeds if it does not explicitly fail.
The actual value returned by the validator is irrelevant.

How does a validator fail?
It does so by using the :hsobj:`PlutusTx.Builtins.error` builtin.
Some other builtins may also trigger failure if they are used incorrectly (e.g. ``1/0``).

Validator functions
-------------------

We write validator scripts as Haskell functions, which we compile with Plutus Tx into Plutus Core.
The type of a validator function is ``Data -> Data -> Data -> ()``, that is, a function which takes three arguments of type ``Data``, and returns a value of type ``()`` ("unit" or "the empty tuple" -- since the return type doesn't matter we just pick something trivial).

Here are two examples of simple validators that always succeed and always fail, respectively:

.. literalinclude:: BasicValidators.hs
   :start-after: BLOCK2
   :end-before: BLOCK3

If we want to write a validator that uses types other than ``Data``, we'll need to use the functions from ``IsData`` to decode them.
Importantly, ``fromData`` can fail: in our example if the ``Data`` in the second argument is *not* a correctly encoded ``Date`` then it will return ``Nothing``, indicating that it couldn't decode it.
However, a decoding failure indicates a mistake in the transaction that was submitted, and so we can simply fail the validation.

.. important::
   Unfortunately there's no way to provide failure diagnostics when a validator fails on chain -- it just fails.
   However, since transaction validation is entirely deterministic, you'll always be informed of this before you submit the transaction to the chain, so you can debug it locally.

Here's an example that uses our date types to check whether the date which was provided is less than the stored limit in the datum.

.. literalinclude:: BasicValidators.hs
   :start-after: BLOCK3
   :end-before: BLOCK4

Using the validation context
----------------------------

.. Still have issues generating the haddock for plutus-ledger, unfortunately

Validators have access to the :term:`validation context` as their third argument.
This will always be a value of type ``Ledger.Validation.ValidatorCtx`` encoded as ``Data``.

The validation context gives validators a great deal of power, because it allows them to inspect other inputs and outputs of the current transaction.
For example, here is a validator that will only accept the transaction if a particular payment is made as part of it.

.. literalinclude:: BasicValidators.hs
   :start-after: BLOCK4
   :end-before: BLOCK5

This makes use of some useful functions from ``Ledger.Validation`` for working with validation contexts.

Automatically wrapping validator functions
------------------------------------------

It is annoying to have to manually decode all the arguments from ``Data`` and call ``check`` at the end.
Fortunately, we provide the ``Ledger.Typed.Scripts.wrapValidator`` function to do this for you.

.. literalinclude:: BasicValidators.hs
   :start-after: BLOCK5
   :end-before: BLOCK6
