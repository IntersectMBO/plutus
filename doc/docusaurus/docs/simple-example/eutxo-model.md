---
sidebar_position: 10
---

# The EUTXO model, datum, redeemer and script context

On the Cardano blockchain, a transaction contains an arbitrary number of inputs and an arbitrary number of outputs. 
The effect of a transaction is to consume inputs and produce new outputs.

<!-- talking about "UTXO concept" -->

UTXO (unspent transaction output) is the ledger model used by some blockchains, including bitcoin. 
A UTXO is produced by a transaction, is immutable, and can only be spent once by another transaction. 
In the original UTXO model, a UTXO contains a wallet address and a value (e.g., some amount of one or more currencies/tokens). 
Inside a transaction, a UTXO is uniquely identified by the wallet address. 
It can be spent by a transaction if the transaction is signed by the private key of the wallet address.

<!-- talking about "EUTXO concept" -->

The Extended UTXO model (EUTXO) extends the original model with a new kind of UTXO: script UTXO. 
A script UTXO contains a value, a script (usually a Plutus script), a piece of data called *datum*, and is identified by the hash of the script. 
For a transaction to spend it, the transaction must provide a piece of input data to the script, referred to as the *redeemer*. 
The script is then run, and it must succeed in order for the transaction to be allowed to spend the UTXO. 
In addition to the redeemer, the script also has access to the datum contained in the UTXO, as well as the details of the transaction trying to spend it. 
This is referred to as *script context*.

<!-- talking about "the role of a Plutus script" -->

Note that the only thing a Plutus script does is to determine whether a transaction can spend the script UTXO that contains the script. 
It is *not* responsible for such things as deciding whether it can spend a different UTXO, checking that the input value in a transaction equals the output value, or updating the state of the smart contract. 
Consider it a pure function that returns `Bool`. 
Checking transaction validity is done by the ledger rules, and updating the state of a smart contract is done by constructing the transaction to produce a new script UTXO with an updated datum.

<!-- talking about "predicatable transaction fees" -->

The immutability of UTXOs leads to the extremely useful property of completely predictable transaction fees. 
The Plutus script in a transaction can be run off-chain to determine the fee before submitting the transaction onto the blockchain. 
When the transaction is submitted, if some UTXOs it tries to spend have already been spent, the transaction is immediately rejected without penalty. 
If all input UTXOs still exist, and the Plutus script is invoked, the on-chain behavior would be exactly identical to the off-chain behavior. 
This could not be achieved if transaction inputs were mutable, such as is the case in Ethereum's account-based model.

See also:

- [Working with scripts](../category/working-with-scripts) for further reading about scripts
- [Understanding the Extended UTXO model](https://docs.cardano.org/learn/eutxo-explainer)

