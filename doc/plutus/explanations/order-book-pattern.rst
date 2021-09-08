.. _what_is_the_order_book_pattern:

What is the order book pattern?
===============================

The order book pattern is a way of organising distributed applications on :term:`Cardano`.
The key idea of the order book pattern is to materialise *actions* that act on some state as :term:`UTXOs <UTXO>` on the :term:`ledger`, separating them from the state they act on.
The spending of those UTXOs (applying the action to the state) can be performed by an untrusted third party.
The pattern is helpful for designing applications that follow the :ref:`scalability_guidelines`.

Example: Distributed exchange
-----------------------------

This is the example that gives the order book its name.
A distributed exchange is an app that lets users trade :term:`currency` values in a decentralised fashion, without a central broker.
At the heart of this app is the order book, a list of open buy and sell offers for specific amounts of currency.
Every buy order needs to be matched with a sell order.

**Example 1:** "Buy 2000 PEAR at 15.00 ADA", "Sell 2000 PEAR at 14.95 ADA" are buy and sell orders for PEAR :term:`tokens <token>`.
In this example, the quantities (2000 units) are identical, and the sell price is lower then the buy price, so we could match the two orders directly and keep the difference between buy and sell price as a fee.

**Example 2:** "Buy 2000 PEAR at 15.00 ADA", "Sell 1500 PEAR at 14.95 ADA".
In this case we need to find at least one other sell order for 500 PEAR to make the quantities match up, for example "Sell 500 PEAR at 14.99".
But this isn't the only solution to the problem:
Maybe we can find another buy order and a bigger sell order, so that we can resolve four orders simultaneously.

The example illustrates where the complexity lies in the order book system:
In finding and matching orders in a way that is profitable for the match maker (broker).

Orders and Plutus scripts
~~~~~~~~~~~~~~~~~~~~~~~~~

The order book lends itself to a nice representation in the EUTXO model.
Every order is a single UTXO, and matching a set of orders means building a transaction that spends the relevant UTXOs.
The UTXOs are script UTXOs with a known address and a datum value that holds the quoted price and some bookkeeping information (for example, an address to pay the money to, and an expiration date).
The currency value locked in the UTXO is the "inverse" of the order.

**Example 3:** "Buy 2000 PEAR at 15.00 ADA" results in a script UTXO with 2000 * 15 = 30,000 ADA. "Sell 2000 PEAR at 14.95 ADA" gives a UTXO with 2000 PEAR tokens.
The match maker can build a transaction that spends the two UTXOs, pays 2000 PEAR tokens to the buyer, 29,000 ADA to the seller and the difference (100 ADA) to the match maker without ever owning any PEAR tokens.

Decentralisation
~~~~~~~~~~~~~~~~

It is clear that the match maker is a crucial component of the system.
Without someone monitoring the script address and building transactions that match buy orders with sell orders, the orders will never be fulfilled.
How can we make sure that the match maker does not become too powerful or too centralised?

We can achieve decentralisation by open-sourcing the scripts that lock the order outputs.
With this code available to the public, anyone can build and run a match-making service and earn fees from matching buy and sell orders.
There could even be a specialised :term:`PAB` available for download somewhere that only runs the match making service, allowing non-programmer users to run nodes for the DEX.

There is no risk of tokens being stolen because the Plutus script ensures that the outputs can only be spent if the order is met exactly as specified.
And while it is possible that the spending transactions suffer from :term:`UTXO congestion <utxo congestion>` (if multiple transactions that match a particular order are submitted), this does not have a negative impact on the user experience, because the buyer or seller does not care which particular match maker ends up fulfilling their order.
In fact, match makers are incentivised to compete by providing faster fulfilment of orders, which actually results in a better outcome for end users.

Generalising the pattern
------------------------

The original application matches buyers and sellers of currency values, but there are other areas where the pattern is useful.

Off-chain oracles
~~~~~~~~~~~~~~~~~

Imagine a Plutus script that says "If you give me a the current USD/EUR exchange rate signed by a specific private key, then I will pay you 5 ADA (and use the exchange rate to run the rest of my `$BUSINESS_LOGIC`)".
The match maker then builds a transaction that combines the oracle value with the Plutus script.
Of course this example requires the match maker to be able to obtain the signed value, but it does succeed in decoupling consumers of the information from  producers.

On-chain oracles
~~~~~~~~~~~~~~~~

The pattern could also be a building block for on-chain oracles.

Let's say we have a crypto-backed stablecoin, not too dissimilar to `Djed <https://iohk.io/en/blog/posts/2021/08/18/djed-implementing-algorithmic-stablecoins-for-proven-price-stability/>`_, that relies on recent quotes of the exchange rate between Ada and PEAR tokens.
And we have a DEX like the one described above where Ada and PEAR are actively traded.
Every order fulfilled on the DEX gives us a snapshot of the exchange rate at that time.
Example 1 from above would result in "15.00 ADA / PEAR" (using the buy price here but that's just a technicality).

This is exactly the information that we need for our dealings with the stablecoin, but how do we get it from the DEX to the stablecoin?
There are two options.
To choose the right one we need to consider the requirement and usage patterns of our application.

1. Oracle UTXOs
...............

We could change the DEX contract to produce a new script UTXO for each fulfilled order that records the time and exchange rate of the order.
The stablecoin user creates a UTXO with a script that requires an oracle UTXO to be present in the spending transaction, and the match maker would put the oracle UTXO and the stablecoin-action UTXO into one transaction and submit it.

2. Oracle tokens
................

In a variation of the first idea, the DEX could produce *tokens* that encode the script-certified information we are interested in.
We could set the asset name of the token to be the hash of the exchange rate data, and allow the transaction to produce any quantitiy of these tokens when the order is fulfilled.

The :term:`minting policy <minting policy script>` of the oracle token should allow any number of tokens of the same asset name to be created as long as at least one token with that asset name exists already, reflecting the idea that information is hard to obtain but easy to replicate.

The consumer of the oracle token needs to check that a token with the expected minting policy hash is present in the transaction, and that the datum value of the token's asset name is available.
Then it can use the information from the datum.
Maybe it could even destroy the token when it has been used.

This approach has the advantage of not clogging up the UTXO set too much, but the big question here is:
How do we make the oracle token available to the match maker?
It has to be stored in an output that the match maker can spend.
The solution depends on the project.
There is no general solution (yet) and some experimentation and research is needed.
Perhaps the tokenomics of the exchange could have incentives to make this information flow to where it is needed.

State machines
~~~~~~~~~~~~~~

State machines are a way of modeling smart contracts that is easy to understand and reason about.
However, in their basic formulation they keep the entire state of each individual execution in a single UTXO, which puts them at risk of UTXO congestion caused by multiple users trying to transition the instance to a new state at the same time.

If we can batch multiple transitions into one (for example, by finding a suitable `Semigroup` instance for the state machine's input type) then we could use the order book pattern to allow a number of users to submit transitions *without spending the UTXO* with the state machine instance's state.
The match maker would construct a transaction that applies the sum of all proposed transitions in a single step.
IOG is actively pursuing research in this area.

Conclusion
----------

In the order book pattern we materialise *actions* as transaction outputs on the ledger, separating them from the state that they act on.
The pattern is attractive because it decouples submission of orders (actions, requests for oracle values, etc) from fulfilling them, and because it enables order fulfilment to be run in a fully decentralised, trustless fashion.
At the same time it fits the UTXO model very well, because it reduces the number of data dependencies on a single unspent output.
