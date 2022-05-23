.. _plutus_language_changes:

Plutus language changes
=======================

Language versions
-----------------

See the documentation on :ref:`language versions <what_are_plutus_language_versions>` for an explanation of what they are.

PlutusV1
~~~~~~~~

``PlutusV1`` was the initial version of Plutus, introduced in the Alonzo hard fork.

PlutusV2
~~~~~~~~

``PlutusV2`` was introduced in the Vasil hard fork.

The main changes in ``PlutusV2`` were to the interface to scripts.
The ``ScriptContext`` was extended to include the following information:

- Redeemers for inputs other than the one currently being validated
- Reference inputs in the transaction (proposed in `CIP-31 <https://cips.cardano.org/cips/cip31/>`_)
- Inline datums in the transaction (proposed in `CIP-32 <https://cips.cardano.org/cips/cip32/>`_)
- Reference scripts in the transaction (proposed in `CIP-33 <https://cips.cardano.org/cips/cip33/>`_)

Built-in functions and types
----------------------------

Built-in functions and types can be introduced with just a hard fork, so this section indicates in which hard fork particular built-ins were introduced.

Alonzo
~~~~~~

This is when the majority of the built-in types and functions were added to ``PlutusV1``.
You can find an enumeration of them in :cite:t:`plutus-core-spec`.

Vasil
~~~~~

All of the built-in types and functions from ``PlutusV1`` were added to ``PlutusV2``.

The following built-in functions were added to ``PlutusV2`` only (not ``PlutusV1``).

- ``serializeData`` (proposed in CIP-42)
- ``verifyEcdsaSecp256k1Signature`` (proposed in CIP-49)
- ``verifySchnorrSecp256k1Signature`` (proposed in CIP-49)
