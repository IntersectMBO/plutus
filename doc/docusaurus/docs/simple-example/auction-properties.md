---
sidebar_position: 15
---

# Auction properties

In this example, Alice wants to auction some asset she owns, represented as a non-fungible token (NFT) on Cardano. 
She would like to create and deploy an auction smart contract with the following properties:

- there is a minimum bid amount
- each bid must be higher than the previous highest bid (if any)
- once a new bid is made, the previous highest bid (if it exists) is immediately refunded
- there is a deadline for placing bids; once the deadline has passed, new bids are no longer accepted, the asset can be transferred to the highest bidder (or to the seller if there are no bids), and the highest bid (if one exists) can be transferred to the seller.

Next, let's go through and discuss the Plutus Tx code we're using, in the next section, for this specific example of an auction smart contract.
