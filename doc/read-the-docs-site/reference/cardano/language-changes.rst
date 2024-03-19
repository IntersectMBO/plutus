.. _plutus_language_changes:

Plutus language changes
=======================

Language versions
-----------------

See the documentation on :ref:`language versions <what_are_plutus_language_versions>` for an explanation of what they are.

PlutusV1
~~~~~~~~~~

``PlutusV1`` was the initial version of Plutus, introduced in the Alonzo hard fork.

PlutusV2
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

- `PlutusV2 functionalities <https://github.com/input-output-hk/cardano-node-wiki/blob/main/docs/reference/plutus/babbage-script-example.md>`_
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

The following built-in function was added to ``PlutusV2`` only (ie, it is not available in ``PlutusV1``).

- ``serializeData`` (proposed in `CIP-42 <https://cips.cardano.org/cips/cip42/>`_)

PlutusV3
~~~~~~~~~

Plutus and cryptography teams at IOG, in collaboration with `MLabs <https://mlabs.city/>`_, continue to develop Plutus capabilities. Starting with the release of `Cardano node v.8.8.0-pre <https://github.com/IntersectMBO/cardano-node/releases/tag/8.8.0-pre>`_, ``PlutusV3`` is available on `SanchoNet <https://sancho.network/>`_, introducing the Cardano community to governance features from `CIP-1694 <https://cips.cardano.org/cip/CIP-1694#goal>`_ in a controlled testnet environment. 

``PlutusV3`` is the new ledger language that enhances Plutus Core's cryptographic capabilities, offering the following benefits for the smart contract developer community: 

- Providing an updated script context that will let users see `CIP-1694 <https://cips.cardano.org/cip/CIP-1694#goal>`_  governance-related entities and voting features
- Interoperability between blockchains
- Advanced Plutus primitives
- Well-known and optimal cryptographic algorithms
- Support for porting of smart contracts from Ethereum
- Creating sidechain bridges
- Improving performance by adding a sums of products (SOPs) feature to support the direct encoding of differrent data types.

Sums of products
~~~~~~~~~~~~~~~~

``PlutusV3`` introduces sums of products - a way of encoding data types that leads to smaller and cheaper scripts compared with `Scott encoding <https://en.wikipedia.org/wiki/Mogensen%E2%80%93Scott_encoding>`_, a common way of encoding data types in Plutus Core. 

The sums of products approach aims to boost script efficiency and improve code generation for Plutus Core compilers. The changes involve new term constructors for packing fields into constructor values and efficient tag inspection for case branches, potentially running programs 30% faster. For an in-depth discussion, see `CIP-85 <https://cips.cardano.org/cip/CIP-0085>`_. 

New cryptographic primitives
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

``PlutusV3`` provides new built-in primitives that expand the language's capabilities. 

- **BLS12-381**: A curve pairing that includes 17 primitives that support cryptographic curves. This is a benefit to sidechain specification implementation and `Mithril <https://iohk.io/en/blog/posts/2023/07/20/mithril-nears-mainnet-release/>`_ integration. 
- **Blake2b-224**: A cryptographic hash function for on-chain computation of public-key hashes for the validation of transaction signatures. Supports community projects and contributes to Cardano's versatility. 
- **Keccak-256**: A cryptographic hash function that produces a 256-bit (32-byte) hash value, commonly used for secure data verification. Supports Ethereum signature verification within scripts and cross-chain solutions. 

Bitwise primitives
~~~~~~~~~~~~~~~~~~~

PlutusV3 initially brings several new bitwise primitives (with more to come at later stages). The introduction of `CIP-58 <https://cips.cardano.org/cip/CIP-0058>`_ bitwise primitives will enable the following features: 

- Very low-level bit manipulations within Plutus, supporting the ability to execute high-performance data manipulation operations. 
- Supporting the implementation of secure and robust cryptographic algorithms within Plutus. 
- Facilitating standard, high-performance implementations for conversions between integers and bytestrings. 

``PlutusV3`` adds two bitwise primitives: ``integerToByteString`` and ``byteStringToInteger``. The remaining primitives will be added to ``PlutusV3`` gradually and will not require a new ledger language. 
