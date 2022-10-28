.. _plutus_language_changes:

Plutus language changes
=======================

Language versions
-----------------

See the documentation on :ref:`language versions <what_are_plutus_language_versions>` for an explanation of what they are.

Plutus V1
~~~~~~~~~~

``PlutusV1`` was the initial version of Plutus, introduced in the Alonzo hard fork.

Plutus V2
~~~~~~~~~~

``PlutusV2`` was introduced in the Vasil hard fork.

The main changes in ``PlutusV2`` were to the interface to scripts.
The ``ScriptContext`` was extended to include the following information:

- The full "redeemers" structure, which contains all the redeemers used in the transaction
- Reference inputs in the transaction (proposed in `CIP-31 <https://cips.cardano.org/cips/cip31/>`_)
- Inline datums in the transaction (proposed in `CIP-32 <https://cips.cardano.org/cips/cip32/>`_)
- Reference scripts in the transaction (proposed in `CIP-33 <https://cips.cardano.org/cips/cip33/>`_)

Examples
------------

- `Plutus V2 functionalities <https://github.com/input-output-hk/cardano-node/blob/master/doc/reference/plutus/babbage-script-example.md>`_
- `How to use reference inputs <https://github.com/perturbing/vasil-tests/blob/main/reference-inputs-cip-31.md>`_
- `How to use inline datums <https://github.com/perturbing/vasil-tests/blob/main/inline-datums-cip-32.md>`_
- `How to reference scripts <https://github.com/perturbing/vasil-tests/blob/main/referencing-scripts-cip-33.md>`_
- `How to use collateral outputs <https://github.com/perturbing/vasil-tests/blob/main/collateral-output-cip-40.md>`_

Built-in functions and types
----------------------------

Built-in functions and types can be introduced with just a hard fork.
In some cases they are also available only in particular language versions.
This section indicates in which hard fork particular built-ins were introduced, and any language version constraints.

Alonzo
~~~~~~

This is when the majority of the built-in types and functions were added to ``PlutusV1``.
You can find an enumeration of them in :cite:t:`plutus-core-spec`.

Vasil
~~~~~

All of the built-in types and functions from ``PlutusV1`` were added to ``PlutusV2``.

The following built-in function was added to ``PlutusV2`` only (i.e., it is not available in ``PlutusV1``).

- ``serializeData`` (proposed in `CIP-42 <https://cips.cardano.org/cips/cip42/>`_)
