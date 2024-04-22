# Writing the On-Chain Validator

The `main` function in `Main.hs` does two things:

* Instantiate the validator by providing the `AuctionParams` of a specific auction
* Serialise the instantiated validator and write it to a file


Replace `apSeller` with the seller's [PubKeyHash](https://intersectmbo.github.io/plutus/master/plutus-ledger-api/html/PlutusLedgerApi-V2.html#t:PubKeyHash), which can be generated using Cardano CLI, Cardano API or an off-chain library for Cardano.

Replace `apEndTime` with your desired [POSIXTime](https://intersectmbo.github.io/plutus/master/plutus-ledger-api/html/PlutusLedgerApi-V2.html#t:POSIXTime).

Now, build it: 
```
cabal build plutus-tx-template
```

Then, run the executable with: 
```
cabal exec plutus-tx-template
```

This should succeed and will write the serialised validator to `validator.uplc`.

Congratulations - you've successfully created a Plutus validator script.

### Creating and Submitting Transactions using an Off-Chain Framework

Once you have the validator, you can proceed with deploying and interacting with a smart contract that uses this validator.
To do so, you'll need the ability to perform operations like the following:

* Generating key pairs
* Querying available UTXOs that satisfy certain criteria and can be used as the input of a transaction
* Building transactions and calculating transaction fees
* Signing and submitting transactions

These can be done using low-level Cardano CLI commands or the Cardano API library functions.
A better way is to use high-level off-chain libraries and frameworks, such as:

* [Lucid](https://lucid.spacebudz.io/), a JavaScript off-chain library for Cardano
* [Kuber](hhttps://github.com/dQuadrant/kuber), which provides a Haskell library and a JSON API for working with Cardano transactions
* [cardano-transaction-lib](https://github.com/Plutonomicon/cardano-transaction-lib), a PureScript library for building Cardano transactions

These frameworks either consume compiled validators in serialised form (such as the one you just made), or depend on the Plutus Tx library and compile the on-chain code from source.
Refer to their respective documentation for more details about how to use them.

A good way to quickly deploy and test a smart contract is to do it on a public testnet, such as Preview.
Generate a key pair, go to the [faucet](https://docs.cardano.org/cardano-testnet/tools/faucet/) for the testnet you are using to request some funds, submit a transaction to lock the funds in your smart contract validator script, and off you go to have all the fun with it.
Read [Simple Example](https://plutus.readthedocs.io/en/latest/simple-example.html#life-cycle-of-the-auction-smart-contract) if you need to understand how one can submit transactions to interact with the auction smart contract.

### Interfacing between Plutus Tx and Off-Chain Frameworks

At this time, interfacing between Plutus Tx and most off-chain frameworks (especially non-Haskell ones) isn't very well supported.
What this means is that you may run into inconveniences like these:

* An off-chain framework may expect serialised validators to be in a format different than that produced by Plutus Tx.
* The redeemer type is defined in Haskell (e.g., `AuctionRedeemer` in `AuctionValidator.hs`), but needs to be redefined in another language when using a non-Haksell off-chain framework.
  For instance, when using Lucid, you'll need to define an object in JavaScript corresponding to `AuctionRedeemer` in order to construct your redeemer.

These inconveniences will be addressed once Plutus contract blueprints, as outlined in [CIP-0057](https://developers.cardano.org/docs/governance/cardano-improvement-proposals/cip-0057/), are adopted and implemented by us as well as the off-chain frameworks.
