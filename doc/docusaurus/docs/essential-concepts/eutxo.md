---
sidebar_position: 20
---

# Scripts and the Extended UTXO Model

## Account-based and UTXO-based Ledgers

There are two dominant paradigms for implementing distributed ledgers that manage and track the ownership of assets.
The first, account-based ledgers, model the system as a list of mutable accounts, as in

| Owner | Balance |
|-------|---------|
| Alice | 43 USD  |
| Bob   | 12 USD  |

A transaction can decrease the balance of the sender, and increase the balance of the recipient.

Account-based ledgers, such as Ethereum, are relatively simple to implement, but they have disadvantages due to the fact that the state of an account is global: all transactions that do anything with an account must touch this one value.
This can lead to issues with throughput, as well as ordering issues (if Alice sends 5 USD to Bob, and Bob sends 5 USD to Carol, this may succeed or fail depending on the order in which the transactions are processed).

The second paradigm is UTXO-based ledgers, such as Bitcoin, which represent the state of the ledger as a set of unspent
transaction outputs (UTXOs).
A UTXO is like an envelope with some money in it: it is addressed to a particular party, and it contains some assets.
A transaction spends some number of UTXOs, and creates new ones.
A UTXO is immutable and can only be spent once.

So a transaction that sends 5 USD from Alice to Bob would do so by spending some number of already existing UTXOs belonging to Alice, and creating a new UTXO with 5 USD belonging to Bob.

UTXO-based ledgers are more complicated, but avoid some of the issues of account-based ledgers, since any transaction deals only with the inputs that it spends.
Cardano is a UTXO-based ledger.

## The Extended UTXO Model

In the classic UTXO model, each UTXO's address includes a public key (strictly, the hash of a public key), and in order to spend this output, the spending transaction must be signed by the corresponding private key.
We call this UTXO a public key UTXO, and its address a public key address.

Cardano uses an extended model called the Extended UTXO Model (EUTXO).
In the EUTXO model, a UTXO's address may include the hash of a script.
We call this UTXO a script UTXO, and its address a script address.

Spending a script UTXO does not require a signature, but instead, requires the script whose hash matches the UTXO address to be included either directly in the transaction, or in a reference input referenced by the transaction.
The script runs to determine if the transaction is authorized to spend the UTXO.
Scripts can also validate other actions transactions perform, such as minting and burning tokens, withdrawing staking rewards, voting, and more.
For further details, see [Script Purposes](../working-with-scripts/script-purposes.md).

A simple script would be one that checks whether the spending transaction is signed by a particular public key.
This would mirror the functionality of simple public key outputs.
However, scripts allow us to implement a wide range of useful logic on the blockchain.

To learn more about writing scripts, see [Using Plinth](../category/using-plinth) and [Working with scripts](../category/working-with-scripts).
