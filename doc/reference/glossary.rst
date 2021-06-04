.. _glossary:

Glossary
========

.. glossary::
    active endpoint
      An endpoint that is active on a contract application instance. Indicates that the contract application instance is waiting for input. The set of active endpoints is part of the state of the contract application instance and changes over time.

    address
      The address of an UTXO says where the output is "going". The address
      stipulates the conditions for unlocking the output. This can be a
      public key hash, or (in the Extended UTXO model) a script hash.

    Cardano
      The blockchain system upon which the Plutus Platform is built.

    contract application
      An application written against the contract application API, which
      runs in the PAB.

    contract application API
      The API that provides an interface between a contract application and
      the PAB. Also allows the contract to declare contract endpoints that
      will be forwarded on to PAB clients via the application interface.

    contract application instance
      A configured, running instance of a contract application.
      Configuration and initialization may require additional parameters to
      be set by the user. Has its state and lifecycle managed by the PAB.

    contract endpoint
      An interface point exposed by a contract application as part of its
      own API. These are forwarded on by the PAB to the wallet frontend or
      other clients.

    contract executable
      A compiled executable of a contract application. These are what are
      actually distributed to users and run by the PAB.

    currency
      A class of token whose forging is controlled by a particular monetary
      policy script. On the Cardano ledger there is a special currency
      called Ada which can never be forged and which is controlled
      separately.

    datum
      The data field on script outputs in the Extended UTXO model.

    endpoint
      A potential request made by a contract application for user input. Every endpoint has a name and a type.

    Extended UTXO Model
      The ledger model which the Plutus Platform relies on.

      This is implemented in the Alonzo hard fork of the Cardano blockchain.

      See :ref:`what_is_a_ledger`.

    forging
      A transaction which forges tokens creates new tokens, providing that
      the corresponding monetary policy script is satisfied. The amount
      forged can be negative, in which case the tokens will be destroyed
      instead of created.

    forging context
      A data structure containing a summary of the transaction being
      validated, and the current forging policy which is being run.

    forging policy script
      A script which must be satisfied in order for a transaction to forge
      tokens of the corresponding currency.

    Hydra
      A Layer 2 scalability solution for Cardano. See :cite:t:`chakravarty2020hydra`.

    distributed ledger
    ledger
      See :ref:`what_is_a_ledger`.

    Marlowe
      A domain-specific language for writing financial contract
      applications.

    multi-asset
      A generic term for a ledger which supports multiple different
      asset types natively.

    off-chain code
      The part of a contract application’s code which runs off the chain,
      usually as a contract application.

    on-chain code
      The part of a contract application’s code which runs on the chain
      (i.e. as scripts).

    PAB client API
      The API that the PAB provides to allow PAB clients to interact with
      contract application instances. Contract endpoints which are exposed
      by running instances can be called via the client API.

    PAB client
      A program which interacts with a contract application instance via
      the PAB’s client API. Examples of PAB clients include:

      1. Wallet frontends such as Daedalus.

      2. Other user software which uses the contract application as part of a wider system.

    Plutus Application
      An application written using the Plutus Application Framework.

    Plutus Application Backend (PAB)
      The component which manages Plutus Applications that run on users' machines.
      It handles:

      1. Interactions with the node

      2. Interactions with the wallet backend

      3. Interactions with the wallet frontend

      4. State management

      5. Tracking historical chain information

    Plutus Core
      The programming language in which scripts on the Cardano blockchain
      are written. Plutus Core is a small functional programming
      language — a formal specification is available with further details.
      Plutus Core is not read or written by humans, it is a compilation
      target for other languages.

      See :ref:`what_is_plutus_foundation`.

    Plutus IR
      An intermediate language that compiles to Plutus Core. Plutus IR is
      not used by users, but rather as a compilation target on the way to
      Plutus Core. However, it is significantly more human-readable than
      Plutus Core, so should be preferred in cases where humans may want to
      inspect the program.

    Plutus Platform
      The combined software support for writing contract applications,
      including:

      1. Plutus Foundation, and

      2. The Plutus Application Framework

      See :ref:`what_is_the_plutus_platform`.

    Plutus SDK
      The libraries and development tooling for writing contract
      applications in Haskell.

    Plutus Tx
      The libraries and compiler for compiling Haskell into Plutus Core to
      form the on-chain part of a contract application.

    redeemer
      The argument to the validator script which is provided by the
      transaction which spends a script output.

    schema
      The set of all endpoints of a contract application.

    script
      A generic term for an executable program used in the ledger. In the
      Cardano blockchain, these are written in Plutus Core.

    script output
      A UTXO locked by a script.

    token
      A generic term for a native tradeable asset in the ledger.

    UTXO
      An "unspent transaction output". Transactions produce these, and they
      are consumed when they are spent by another transaction. Typically,
      some kind of evidence is required to be able to spend a UTXO, such as
      a signature from a public key, or (in the Extended UTXO Model)
      satisfying a script.

    validator script
      The script attached to a script output in the Extended UTXO model.
      Must be run and return positively in order for the output to be
      spent. Determines the address of the output.

    validation context
      A data structure containing a summary of the transaction being
      validated, and the current input whose validator is being run.
