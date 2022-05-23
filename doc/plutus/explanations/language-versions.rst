.. _what_are_plutus_language_versions:

What are Plutus language versions?
==================================

The Cardano ledger tags scripts with a *language*.
This determines how the ledger will interpret the script, but also the *interface* to the script.
The interface is very important, since it governs what arguments the ledger will provide to the script, including what information about the transaction is conveyed.
Today, the main languages are the "simple" script language (which allows basic timelocks etc.) and multiple versions of Plutus (we'll discuss what that means below).

Languages must continue to behave the same forever, otherwise we could change the behaviour of existing scripts, potentially making outputs un-spendable and breaking users' assumptions.
That means that many kinds of change to the behaviour of the language instead require a "new" language. [1]_

Hence, in order to change Plutus, we need to create a new language in the ledger.
Since in most cases this language will be very similar to the ones that came before, we refer to these as "Plutus language versions".
This is a little confusing since it may be that the only difference between "language versions" is that the interface to scripts has changed, and not the Plutus Core language itself.
However, this reflects the fact that from the *ledger's* perspective this is a new, completely independent language.

In practice, the process for creating scripts of different Plutus language versions is very similar.
The main difference is that you will likely need a different ``ScriptContext`` type, and different built-in functions may be available.
See :ref:`Plutus language changes <plutus_language_changes>` for a description of what has changed between versions.

.. [1] For more details about what kinds of change require a new language , see the `Plutus Evolution CIP <https://cips.cardano.org/cips/cip35/>`_.
