# Cardano Streaming

cardano-streaming is a simple library that wraps cardano-api giving a
streaming interface to the chain-sync protocol. This means you can use this
library to stream blocks from a locally running node.

The blocks are presented as received from the chain-sync protocol so you
will still need to use function from `Cardano.Api` (in cardano-node) or
`Plutus.Ledger`(in plutus-ledger) to extract information from blocks.

# Example applications

## Example 1

This application simply streams to stdout events in JSON format.

## Example 2

This application uses plutus-ledger to extract transactions (transaction
id, ins and outs) and datums. Then it prints them to stdout in JSON format.

## Example 3

This application uses folds the stream into a UTxoState as defined in
plutus-chain-index-core.

# Running the example applications

You can run the example applications with cabal. Remember you need to have
a local node running and reachable through the provided socket.

From Genesis

```
$ cabal run -- cardano-streaming-example-1 --socket-path /tmp/node.socket --mainnet
```

Passing a starting point

```
$ cabal run -- cardano-streaming-example-1 --socket-path /tmp/node.socket --slot-no 53427524 --block-hash 5e2bde4e504a9888a4f218dafc79a7619083f97d48684fcdba9dc78190df8f99
```
