.. _quick_start:

Quick Start
=================================

This guide gets you started on setting up the dev environment for a simple Cardano smart contract, with the on-chain validator written in Plutus Tx.
There are several other options for writing on-chain validators, such as `Aiken <https://aiken-lang.org/>`_ and `OpShin <https://github.com/OpShin/opshin>`_, and you can refer to their respective documentation for how to use them.

Writing the On-Chain Validator
-----------------------------------------------------------------

Prerequisites
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

GHC and Cabal should be installed in order to follow this guide.
Plutus Tx currently supports GHC v9.2.x and v9.6.x.
Cabal v3.8+ is recommended.

Additionally, some C libraries will need to be installed.
Plutus Tx depends on `cardano-base <https://github.com/input-output-hk/cardano-base>`_, which in turn depends on a few cryptographic C libraries, including ``libblst``, ``libsecp256k1``, and ``libsodium``.
Cabal is not designed to manage C dependencies, so you need to either install them yourself, or manage them using another tool (such as Nix).

If you are not using Nix, follow the instructions in `cardano-base <https://github.com/input-output-hk/cardano-base>`_ or `cardano-node <https://github.com/input-output-hk/cardano-node-wiki/blob/main/docs/getting-started/install.md>`_ to install these libraries (or install them in your own way if you like).

If you are using Nix, you can use plutus repository's dev shell: ::

  nix develop github:input-output-hk/plutus

The dev shell comes with not only the required C libraries, but also GHC and Cabal.

Create a New Cabal Package
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

First, make a new directory ``plutus-quickstart``: ::

  mkdir plutus-quickstart && cd $_

Then, create a new Cabal package that builds an executable, using default settings: ::

  cabal init --exe --non-interactive

Declare Plutus Tx Dependencies
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Next we have to add some packages as dependencies. The Plutus packages aren't on Hackage (the default repository Cabal looks for packages from), but on the `CHaP <https://github.com/input-output-hk/cardano-haskell-packages>`_ repository.
Therefore, we need to tell Cabal to look for packages from CHaP (in addition to Hackage).
To do so, make a ``cabal.project`` file, and follow the `instructions <https://github.com/input-output-hk/cardano-haskell-packages#using-chap>`_ in the CHaP repository to make Cabal aware of CHaP.
Then, add the following to your ``cabal.project``: ::

  packages:
    ./plutus-quickstart.cabal

Finally, declare the dependencies in the ``build-depends`` field in ``plutus-quickstart.cabal``: ::

  build-depends:
    , base
    , base16-bytestring
    , bytestring
    , plutus-core
    , plutus-ledger-api
    , plutus-tx
    , plutus-tx-plugin

At this point, you should be able to build your project: ``cabal build plutus-quickstart`` should succeed.

Write the Validator
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Now we are ready to write the on-chain validator using Plutus Tx.
We showed and explained an auction validator in :ref:`simple_example`, and we'll reuse the same validator here.
Make a file named ``AuctionValidator.hs`` in the ``app`` directory, and copy the content over from `here <https://github.com/input-output-hk/plutus/blob/master/doc/read-the-docs-site/tutorials/AuctionValidator.hs>`_.
Then, Add the following in ``plutus-quickstart.cabal``: ::

  other-modules:
    AuctionValidator

Note that ``AuctionValidator.hs`` imports ``ScriptContext`` from ``PlutusLedgerApi.V2``, which means that the script created from it will be a PlutusV2 script.
PlutusV2 only supports Plutus Core v1.0.0 (currently the highest and default version is v1.1.0), which is why the ``target-version=1.0.0`` flag is needed.

Next, write the ``main`` function in ``Main.hs``, which does two things:

* Instantiate the validator by providing the ``AuctionParams`` of a specific auction
* Serialise the instantiated validator and write it to a file

Here is what ``Main.hs`` may look like:

.. literalinclude:: tutorials/QuickStart.hs
   :start-after: BLOCK1
   :end-before: BLOCK2

Replace ``apSeller`` with the seller's `PubKeyHash <https://input-output-hk.github.io/plutus/master/plutus-ledger-api/html/PlutusLedgerApi-V2.html#t:PubKeyHash>`_, which can be generated using Cardano CLI, Cardano API or an off-chain library for Cardano.
Replace ``apEndTime`` with your desired `POSIXTime <https://input-output-hk.github.io/plutus/master/plutus-ledger-api/html/PlutusLedgerApi-V2.html#t:POSIXTime>`_.

Now, build it: ::

  cabal build plutus-quickstart

This should succeed and will write the serialised validator to ``validator.uplc``.
Congratulations - you've successfully created a Plutus validator script.

Creating and Submitting Transactions using an Off-Chain Framework
-----------------------------------------------------------------

Once you have the validator, you can proceed with deploying and interacting with a smart contract that uses this validator.
To do so, you'll need the ability to perform operations like the following:

* Generating key pairs
* Querying available UTXOs that satisfy certain criteria and can be used as the input of a transaction
* Building transactions and calculating transaction fees
* Signing and submitting transactions

These can be done using low-level Cardano CLI commands or the Cardano API library functions.
A better way is to use high-level off-chain libraries and frameworks, such as:

* `Lucid <https://lucid.spacebudz.io/>`_, a JavaScript off-chain library for Cardano
* `Kuber <https://github.com/dQuadrant/kuber>`_, which provides a Haskell library and a JSON API for working with Cardano transactions
* `cardano-transaction-lib <https://github.com/Plutonomicon/cardano-transaction-lib>`_, a PureScript library for building Cardano transactions

These frameworks either consume compiled validators in serialised form (such as the one you just made), or depend on the Plutus Tx library and compile the on-chain code from source.
Refer to their respective documentation for more details about how to use them.

A good way to quickly deploy and test a smart contract is to do it on a public testnet, such as Preview.
Generate a key pair, go to the `faucet <https://docs.cardano.org/cardano-testnet/tools/faucet/>`_ for the testnet you are using to request some funds, submit a transaction to lock the funds in your smart contract validator script, and off you go to have all the fun with it.
Read :ref:`simple_example`, section *Life cycle of the auction smart contract* if you need to understand how one can submit transactions to interact with the auction smart contract.

Interfacing between Plutus Tx and Off-Chain Frameworks
-----------------------------------------------------------------

At this time, interfacing between Plutus Tx and most off-chain frameworks (especially non-Haskell ones) isn't very well supported.
What this means is that you may run into inconveniences like these:

* An off-chain framework may expect serialised validators to be in a format different than that produced by Plutus Tx.
* The redeemer type is defined in Haskell (e.g., ``AuctionRedeemer`` in ``AuctionValidator.hs``), but needs to be redefined in another language when using a non-Haksell off-chain framework.
  For instance, when using Lucid, you'll need to define an object in JavaScript corresponding to ``AuctionRedeemer`` in order to construct your redeemer.

These inconveniences will be addressed once Plutus contract blueprints, as outlined in `CIP-0057 <https://developers.cardano.org/docs/governance/cardano-improvement-proposals/cip-0057/>`_, are adopted and implemented by us as well as the off-chain frameworks.
