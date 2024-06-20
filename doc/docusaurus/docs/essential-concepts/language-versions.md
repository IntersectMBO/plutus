---
sidebar_position: 20
---

# Plutus language versions

The Cardano ledger tags scripts with a *language*. 
This determines what the ledger will do with the script.

For example, the 'simple' script language introduced in the Allegra era allows for a few basic kinds of checks to be made, such as time locks. 
To interpret simple scripts, the ledger must (among other things) extract the validation interval information from the transaction to check the conditions imposed by the script.

Plutus scripts, introduced in the Alonzo era, have a more complex interface than simple scripts. 
Plutus scripts are programs written in the Plutus Core programming language that receive three arguments:

1. the datum
2. the redeemer, and
3. the context.

The *context* contains all the information about the transaction which is currently being validated. (See [Scripts and the Extended UTXO model](ledger.md#scripts-and-the-extended-utxo-model) for more details).

Languages must continue to behave the same forever; otherwise, we could change the behaviour of existing scripts, potentially making outputs un-spendable and breaking users' assumptions. 
That means that many kinds of changes to the behaviour of the language instead require a "new" language. 
This includes changes to the interface of the language.

For example, if we want to put more information in the *context* (e.g., in order to convey information about new fields that have been added to transactions), then we need a new language, because old scripts would not be able to understand the new information.

> :pushpin: **NOTE**
> 
> For more details about what kinds of changes require a new language, see the Cardano Improvement Proposal, [CIP 35&mdash;Plutus Core Evolution](https://cips.cardano.org/cips/cip35/).

Therefore, to change Plutus, we need to create a new language in the ledger. 
Since, in most cases, this language will be very similar to the ones that came before, we refer to these as 'Plutus language versions.'
However, from the ledger's perspective, they are entirely unrelated and there is generally no requirement that they be similar or compatible in any way.

There are two different uses of 'language' here that are important to keep distinct:

1. Plutus Core is a *programming* language in which Plutus scripts are written
2. Plutus (the Plutus Core programming language and a particular interface) is a 'language' in the terminology of the ledger.

In particular, a specific version of the Plutus Core programming language may be used in multiple versions of the Plutus ledger language, if, for example, the only difference is to the interface. 
To date, all versions of Plutus use the same version of the Plutus Core. 
That means that, in practice, the process for creating scripts of different Plutus language versions tends to be similar. 
The main difference is that you will likely need a different `ScriptContext` type, and different
built-in functions may be available.

*See also:*

- [Plutus language changes](../reference/plutus-language-changes.md) for a description of what has changed between versions
- [Upgrading to Vasil and Plutus script addresses](../reference/upgrade-vasil-plutus-script-addresses.md).
