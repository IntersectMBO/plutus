.. _what_is_the_chain_index:

What is the chain index?
========================

The chain index is a content-addressable store for different pieces of on-chain data (datums, redeemer, scripts).
The contents of the store are deleted when there are no more unspent outputs left that reference them.
It uses the Cardano node's chain sync protocol over a socket.
Therefore it needs to run on the same machine with a Cardano node.
The chain index is a read-only component for the PAB.
Multiple instances of the PAB can share a single instance of the chain index.

The expressiveness of queries supported by the chain index lies somewhere between that of the node, which answers queries related to the ledger state, and that of `Cardano DB Sync <https://github.com/input-output-hk/cardano-db-sync>`_, which has a full history of all transactions and an expressive database schema for staking and other information.

HTTP API
--------

All chain index queries are served over an HTTP API.
The API, defined in the ``Plutus.ChainIndex.Api`` `module <https://github.com/input-output-hk/plutus/blob/master/plutus-chain-index/src/Plutus/ChainIndex/Api.hs>`_, has the following routes:

.. openapi:: ./chain-index-api.yaml
