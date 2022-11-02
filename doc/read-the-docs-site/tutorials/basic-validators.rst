.. highlight:: haskell
.. _basic_validators_tutorial:

Writing basic validator scripts
===============================

:term:`Validator scripts<validator script>` are the programs that can be used to lock transaction outputs on the chain.
Validator scripts are :term:`Plutus Core` programs, but we can use :term:`Plutus Tx` to write them easily in Haskell.
Check out the :ref:`Plutus Tx tutorial<plutus_tx_tutorial>` before reading this one.

Validator arguments
-------------------

Validators receive some information from the validating node:

- The :term:`redeemer`, which is some script-specific data specified by the party spending the output.
- The :term:`datum`, which is some script-specific data specified by the party who created the output.
- The :term:`script context`, which contains a representation of the spending transaction, as well as the index of the input whose validator is currently being run.

The validator is a function which receives these three inputs as *arguments*.
The validating node is responsible for passing them in and running the validator.

The ``Data`` type
-----------------

But how are the validator's arguments passed?
Different scripts are going to expect different sorts of values in their datums and redeemers.

The answer is that we pass the arguments as a *generic* structured data type :hsobj:`PlutusCore.Data.Data`.
``Data`` is designed to make it easy to encode structured data into it, and is essentially a subset of CBOR.

Validator scripts take three arguments of type ``Data``.
Since ``Data`` is represented as a builtin type in Plutus Core, we use a special Haskell type ``BuiltinData`` rather than the underlying ``Data`` type

However, you will typically not want to use ``BuiltinData`` directly in your program, rather you will want to use your own datatypes.
We can easily convert to and from ``BuiltinData`` with the :hsobj:`PlutusTx.IsData.Class.ToData`, :hsobj:`PlutusTx.IsData.Class.FromData`, and :hsobj:`PlutusTx.IsData.Class.UnsafeFromData` typeclasses.
You usually don't need to write your own instances of these classes.
Instead, you can use the ``unstableMakeIsData`` or ``makeIsDataIndexed`` Template Haskell functions to generate one.

.. note::
   The :hsobj:`PlutusTx.IsData.Class.UnsafeFromData` class provides ``unsafeFromBuiltinData``, which is the same as ``fromBuiltinData``, but is faster and fails with ``error`` rather than returning a ``Maybe``.
   We'll use ``unsafeFromBuiltinData`` in this tutorial, but sometimes the other version is useful.

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
The type of a validator function is ``BuiltinData -> BuiltinData -> BuiltinData -> ()``, that is, a function which takes three arguments of type ``BuiltinData``, and returns a value of type ``()`` ("unit" or "the empty tuple" -- since the return type doesn't matter we just pick something trivial).

Here are two examples of simple validators that always succeed and always fail, respectively:

.. literalinclude:: BasicValidators.hs
   :start-after: BLOCK2
   :end-before: BLOCK3

If we want to write a validator that uses types other than ``BuiltinData``, we'll need to use the functions from :hsobj:`PlutusTx.IsData.Class.FromData` to decode them.
Importantly, ``unsafeFromBuiltinData`` can fail: in our example if the ``BuiltinData`` in the second argument is *not* a correctly encoded ``Date`` then it will fail the whole validation with ``error``, which is usually what we want if we have bad arguments.

.. TODO: write a HOWTO about error reporting

.. important::
   Unfortunately there's no way to provide failure diagnostics when a validator fails on chain -- it just fails.
   However, since transaction validation is entirely deterministic, you'll always be informed of this before you submit the transaction to the chain, so you can debug it locally using ``traceError``.

Here's an example that uses our date types to check whether the date which was provided is less than the stored limit in the datum.

.. literalinclude:: BasicValidators.hs
   :start-after: BLOCK3
   :end-before: BLOCK4

Plutus script context versions
------------------------------------

Validators have access to the :term:`script context` as their third argument.
Each version of Plutus validators are differentiated only by their ``ScriptContext`` argument. 

   See this example from the file ``MustSpendScriptOutput.hs`` (lines 340 to 422) showing code addressing `Versioned Policies for both Plutus V1 and Plutus V2 <https://github.com/input-output-hk/plutus-apps/blob/05e394fb6188abbbe827ff8a51a24541a6386422/plutus-contract/test/Spec/TxConstraints/MustSpendScriptOutput.hs#L340-L422>`_. 

The script context gives validators a great deal of power, because it allows them to inspect other inputs and outputs of the current transaction.
For example, here is a validator that will only accept the transaction if a particular payment is made as part of it.

.. literalinclude:: BasicValidators.hs
   :start-after: BLOCK4
   :end-before: BLOCK5

This makes use of some useful functions for working with script contexts.
