---
sidebar_position: 30
---

# Libraries for writing Plutus Tx scripts

This auction example shows a relatively low-level way of writing scripts using Plutus Tx. 
In practice, you may consider using a higher-level library that abstracts away some of the details. 
For example, [plutus-apps](https://github.com/IntersectMBO/plutus-apps) provides a constraint library for writing Plutus Tx. 
Using these libraries, writing a validator in Plutus Tx becomes a matter of defining state transactions and the corresponding constraints, e.g., the condition `refundsPreviousHighestBid` can simply be written as `Constraints.mustPayToPubKey bidder (lovelaceValue amt)`.

