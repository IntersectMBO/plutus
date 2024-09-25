---
sidebar_position: 25
---

# Closing the Auction

Once the auction's end time has elapsed, a transaction can be submitted to finalize the auction, distributing the token and the highest bid accordingly.
This transaction needs to do the following:

- Spend the UTxO that contains the token being auctioned.
- If no bids were placed (which can be determined by examining the datum attached to the UTxO), the token should be returned to the seller's address.
- If at least one bid was placed, the token should be transferred to the highest bidder's address, and the highest bid amount should be sent to the seller's address.
- Set a validity interval that starts no earlier than the auction's end time.

The off-chain code for building and submitting this transaction will be very similar to the code for the bidding transactions, so the details are left as an exercise.
