---
sidebar_position: 10
---

# Getting Funds from the Faucet

Next, we'll need to fund the wallet of each participant (seller, bidder1 and bidder2), in order to cover transaction fees and place bids.
We can get funds from Cardano's [testnet faucet](https://docs.cardano.org/cardano-testnets/tools/faucet/).

To request funds, enter the seller's address into the address field and click "request funds."
This will deposit 10,000 (test) ADA into the seller's wallet.

Since the faucet limits how frequently you can request funds, and 10,000 ADA is more than sufficient for this example, we'll share the 10,000 ADA among the seller, bidder1, and bidder2.
To do so, create a file named `off-chain/send-lovelace.mjs` with the following content:

<LiteralInclude file="send-lovelace.mjs" language="javascript" title="send-lovelace.mjs" />

Substitute your Blockfrost project ID for `Replace with Blockfrost Project ID`.

This Javascript module builds and submits a transaction that sends 1 billion Lovelace (equivalent to 1000 Ada) from the seller's wallet to the specified recipient.
Run the following commands:

```
node send-lovelace.mjs bidder1
node send-lovelace.mjs bidder2
```

After the transactions are confirmed and included in a block (usually within a minute), bidder1's and bidder2's wallets should each have 1000 Ada, and the seller's wallet should have approximately 8000 Ada (minus transaction fees), which you can verify on [Cardanoscan](https://preview.cardanoscan.io/).
