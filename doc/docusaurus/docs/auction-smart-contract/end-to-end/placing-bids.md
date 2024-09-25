---
sidebar_position: 20
---

# Placing Bids

Now we can start bidding.
Let's place a bid of 100 Ada from bidder1, followed by a bid of 200 Ada from bidder2.
Each transaction that places a bid must do the following:

- Spend the UTxO that contains the token being auctioned.
  For bidder1, the transaction that produced the UTxO is the one that minted the token.
  For bidder2, the transaction that produced the UTxO is bidder1's transaction.
  The address of this UTxO is always the auction validator's script address, so each bidding transaction must include the auction validator and a redeemer[^1].
- Place a bid (via the redeemer) with an amount at least as high as the auction's minimum bid, and higher than the previous highest bid (if any).
  The existence and the details of a previous highest bid can be determined by inspecting the datum attached to the aforementioned UTxO.
  This is enforced by the auction validator's `sufficientBid` condition.
- Lock the token being auctioned, together with the bid amount, in a new UTxO at the auction validator's script address.
  The new UTxO should also include a datum containing the details of this bid.
  This is enforced by the auction validator's `correctOutput` condition.
- Refund the previous highest bid (if any) to its bidder's wallet address.
  This is enforced by the auction validator's `refundsPreviousHighestBid` condition.
- Set a validity interval that ends no later than the auction's end time.
  This is enforced by the auction validator's `validBidTime` condition.

To submit these bidding transactions, create a file named `off-chain/bid.mjs` for the off-chain code, with the following content:

<LiteralInclude file="bid.mjs" language="javascript" title="bid.mjs" />

This Javascript module builds and submits a transaction that does exactly the above.

The following substitutions are needed:

- Substitute your Blockfrost project ID for `Replace with Blockfrost Project ID`.
- Substitute a slot number no later than the auction's end time for `Replace with transaction expiration time`.
  For instance, if you set the auction's end time to be approximately 24 hours from now, you can use a slot number corresponding to approximately 12 hours from now.
  To determine the slot nmber, go to [Cardanoscan](https://preview.cardanoscan.io/), click on a recent transaction, take its Absolute Slot, and add 12 hours (43200) to it.

Place the first bid by running

```
node bid.mjs <minting-transaction-hash> bidder1 100000000
```

Replace `<minting-transaction-hash>` with the hash of the transaction we previously submitted for minting the token.
This hash is used by the off-chain code to locate the UTxO that contains the token.

After the first bidding transaction is confirmed, we can submit the second bid from bidder2, with a similar command:

```
node bid.mjs <bidder1-transaction-hash> bidder2 200000000
```

Replace `<bidder1-transaction-hash>` with the hash of the previous transaction.

---

[^1]: Instead of including the script in the transaction, we can use a reference script, but to keep things simple, we won't discuss that here.
