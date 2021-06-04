.. highlight:: haskell
.. _exporting_a_script:

How to export a script
======================

.. note::
    This guide uses the scripts from the :ref:`basic validators tutorial <basic_validators_tutorial>`.

While most :term:`Plutus Application` s use scripts by directly submitting them as part of transactions from the application itself, it can be useful to be able to export a serialized script.
For example, you might want to submit it as part of a manually created transaction with the Cardano node CLI, send it to another party for them to use, or maybe just back it up.

Fortunately, it is quite simple to do this.
You can either translate directly into CBOR using the `Serialise` typeclass from the `serialise` package, or you can create an envelope of the sort used by the Cardano node CLI.

.. TODO: include instructions on the latter once we have support for it

.. literalinclude:: ../tutorials/BasicValidators.hs
   :start-after: BLOCK8
   :end-before: BLOCK9
