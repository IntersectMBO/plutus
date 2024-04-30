---
title: "Core concepts"
description: "A set of definitions of core concepts"
date: 2024-04-11
---

# Section 2. Core concepts

## Resources to inform this section: 
- Blog: [Plutus Tx: compiling Haskell into Plutus Core](https://iohk.io/en/blog/posts/2021/02/02/plutus-tx-compiling-haskell-into-plutus-core/), by Michael Peyton Jones, Feb. 2021
   - This is several years old, but the underlying essential definitions and concepts are still applicable. 
- Draft document: [Smart contracts security and best practices](https://docs.google.com/document/d/1CrWYmG-I-Z2KeB06pPM9TqvjpSgpgt8e4ipLY9vJDKE/edit?usp=sharing) being prepared by Luka Kurnjek, Education team
- [An Introduction to Plutus Core](https://blog.hachi.one/post/an-introduction-to-plutus-core/)

## Core concepts
- Names, terminology, ecosystem
- Ledger
- Scripts and the EUTXO model
- Different kinds of scripts
- Plutus Core
- Plutus Tx
- Plutus Haskell SDK
- Plutus language versions

## Observation to consider
- The reference to the Plutus Application Framework is outdated. Many elements of it are no longer functioning or being supported. For example, the PAB is no longer supported. The Plutus Playground is no longer available and is not being supported. Plutus Apps are no longer supported. I suggest that it would be helpful to find a new way to talk about the Plutus development environment and ecosystem without referencing the “Plutus Application Framework.”

## Understanding the Plutus platform
- What is Plutus?
	- The relationship between Plutus, Haskell, and Cardano
- Anatomy of a smart contract
- A thumbnail sketch of Plutus smart contract developer workflow
   - Most common tasks
- Plutus Components:
	- Plutus Core (The foundational layer, low-level programming language for smart contracts on Cardano.)
	- Plutus Tx (The library for writing high-level Haskell code that gets compiled down to Plutus Core)
- The Extended UTXO Model (EUTXO):
	- How it differs from the account-based model
	- Advantages for smart contracts

> **Note**
> 
> The draft outline above does not directly map to the way that the content below is organized. The content below has been brought over from the existing docs site and will be further edited and possibly reorganized. But it is helpful to get all of this content into one place as a next step. 

# The Plutus Platform

The Plutus Platform is a platform for writing *applications* that interact with a *distributed ledger* featuring *scripting* capabilities, in particular the `Cardano`{.interpreted-text role="term"} blockchain.

<!-- The above link should go to the term in the glossary -->

## Applications

What sort of "applications" are we talking about here? 
Let's think about a pair of users, Alice and Bob, who want to engage in an atomic swap of some assets stored on Cardano.

::: {.uml caption="Alice and Bob doing an atomic swap"}
actor Alice 
actor Bob 
participant Application 
database Cardano

Alice -> Application: I want to do an escrowed swap with Bob, 50 Ada for my Special Token Application -> Ledger: I want to lock up Alice's Special Token so that it can only be unlocked if Bob completes the swap
Ledger -> Application: Ok, that change has settled 
Application -> Bob: Hey, Alice wants to do a swap with you 
Bob -> Application: I want to take up Alice's swap 
Application -> Cardano: I want to spend that locked output with Alice's Special Token while sending 50 of Bob's Ada to Alice 
Ledger -> Ledger: Does this transaction satisfy the conditions that were asked for? Yes it does! Ledger -> Application: Ok, that change has settled 
Application -> Alice: The swap is completed! 
Application -> Bob: The swap is completed!
:::

Alice and Bob don't interact directly, nor do they directly interact with the ledger. 
Very few "smart" blockchain systems encourage their users to interact directly with the chain themselves, since this is usually complex and error-prone. 
Rather, the users interact with some *application* that presents the world in a form that they can understand and interact with.

Of course, such an application must want to do something with the ledger, otherwise you wouldn't need anything new. 
Simple applications might do nothing more than submit basic transactions that transfer assets - imagine a simple "regular payments" application. 
However, our main focus is applications that *do* use smart features in order to have a kernel of trusted code that is validated as part of the ledger.

This enables applications that are not possible otherwise. 
Alice and Bob need trusted logic in order to perform their swap: a "dumb" application could submit the transactions transferring the assets, but would have no recourse against Bob defecting. 
Using the smart features of the ledger ensures that Bob can't take Alice's token unless he *really does* send her the money, and it does this without involving a trusted third party.

Creating and using the trusted kernel of code is the most technically difficult and security-sensitive part of the whole operation.
Nonetheless, writing the rest of the application contains plenty of complexity. 
Amongst other things, an application needs to deal with the software around the ledger (wallets, nodes, etc.); distributed systems issues such as settlement delays, inconsistent state between parties, and rollbacks; and simple user-experience issues like upgrades, state management and synchronization. 
Furthermore, while none of these are quite as security-critical as the trusted kernel, users certainly *can* be attacked through such applications, and even non-malicious bugs are likely to be quite upsetting when a user's money is at stake.

Even simple applications must deal with this complexity, and for more advanced applications that deal with state across time, the difficulty is magnified.

## The Plutus Platform

This is why the Plutus Platform is a *platform*. 
Rather than just providing a few tools to make the bare minimum possible, we aim to support application development in its entirety, all the way through from authoring to testing, runtime support, and (eventually) verification. 
Ultimately, we wrote it because we needed it ourselves to do anything useful.

Conceptually, the Platform breaks down based on which part of the system we're interested in:

-   `Plutus Foundation<what_is_plutus_foundation>`{.interpreted-text role="ref"}: support for writing the trusted kernel of code, and executing it on the chain
-   [The Plutus Application Framework](https://github.com/IntersectMBO/plutus-apps): support for writing applications ("Plutus Applications") in a particular style

<figure>
<img src="platform-architecture.png"
alt="platform-architecture.png" />
<figcaption>A high-level architecture of the Plutus Platform, with an emphasis on applications.</figcaption>
</figure>

## Further reading

The platform is introduced in :cite[plutus-platform-summit]{.title-ref}.

The design of the platform is discussed in :cite[plutus-report]{.title-ref}.

# Ledgers

The `Plutus Platform<what_is_the_plutus_platform>`{.interpreted-text role="ref"} is designed to work with distributed ledgers (henceforth simply "ledgers"). 
Ledgers are typically *implemented* with a blockchain, such as Cardano. 
However, much of the time when we are talking about ledgers we don't care about the underlying
implementation, and so we will just talk about the ledger itself.

> **Note**
> 
> This is not always true: applications do need to care about details of how the underlying blockchain works, because that affects behaviour such as settlement time and rollback policies. As much as possible the Plutus Application Framework tries to shield developers from this complexity, but it is not always possible.

In its simplest form, a ledger is a system that tracks who owns what.

For example:

| Owner | Balance |
|-------|---------|
| Alice | 43 USD  |
| Bob   | 12 USD  |

Ledgers are typically transformed by performing a *transaction* that transfers some assets from one party to another. 
In order to be *valid* a transaction will have to pass some checks, such as demonstrating that the transfer is authorized by the owner of the funds. 
After applying a transaction (say, Alice sends Bob 5 USD), we have a new state of the ledger.

| Owner | Balance |
|-------|---------|
| Alice | 38 USD  |
| Bob   | 17 USD  |

## Account-based and UTXO-based ledgers

There are two dominant paradigms for how to *represent* such a system.
The first, account-based ledgers, model the system exactly as in our example above. 
They keep a list of accounts, and for each account, a balance. 
A transaction simply decreases the balance of the sender, and increases the balance of the recipient.

Account-based ledgers (such as Ethereum) are very simple to implement, but they have difficulties due to the fact that the state of an account is *global*: all transactions that do anything with an account must touch this one number. 
This can lead to issues with throughput, as well as ordering issues (if Alice sends 5 USD to Bob, and Bob sends 5 USD to Carol, this may succeed or fail depending on the order in which the transactions are processed).

The other paradigm is UTXO-based ledgers. 
UTXO-based ledgers (such as Bitcoin) represent the state of the ledger as a set of "unspent
transaction outputs" (UTXOs). 
A UTXO is like an envelope with some money in it: it is "addressed" to a particular party, and it contains some funds. 
A transaction *spends* some number of UTXOs, and creates some more.

So a transaction that sends 5 USD from Alice to Bob would do so by spending some number of already-existing UTXOs belonging to Alice, and creating a new UTXO with 5 USD belonging to Bob.

UTXO-based ledgers are more complicated, but avoid some of the issues of account-based ledgers, since any transaction deals only with the inputs that it spends. 
Cardano is a UTXO-based ledger, and we heavily rely on this. 
For example, `Hydra`{.interpreted-text role="term"}, Cardano's scalability solution, uses the fact that independent parts of the transaction graph can be processed in parallel to improve throughput.

## Scripts and the Extended UTXO Model {#scripts_and_the_eutxo_model}

UTXO-based ledgers typically start out with a very simple model of "ownership" of UTXOs. 
An output will have a public key (strictly, the hash of a public key) attached to it, and in order to spend this output the spending transaction must be signed by the corresponding private key. 
We call this a "pay-to-pubkey" output.

Cardano uses an extended model called the `Extended UTXO Model`{.interpreted-text role="term"} (EUTXO). 
In the EUTXO model, an output can be locked by (the hash of) a *script*. 
We call this a "pay-to-script" output. 
A script is a *program* that decides whether or not the transaction which spends the output is
authorized to do so. 
Such a script is called a validator script, because it validates whether the spending is allowed.

A simple validator script would be one that checked whether the spending transaction was signed by a particular key---this would exactly replicate the behaviour of simple pay-to-pubkey outputs. 
However, with a bit of careful extension, we can use scripts to let us express a large amount of useful logic on the chain.

With the EUTXO model, validator scripts are passed three arguments:

- The *datum*: this is a piece of data attached to the *output* that the script is locking (strictly, again, just the hash is present). This is typically used to carry state.
- The *redeemer*: this is a piece of data attached to the *input* that is doing the spending. This is typically used to provide an input to the script from the spender.
- The *context*: this is a piece of data which represents information about the transaction doing the spending. This is used to make assertions about the way the output is being sent (such as "Bob signed it").

As an example, let's see how we could implement an atomic swap.

- The datum contains the keys of the two parties in the swap, and a description of what they are swapping.
- The redeemer is unused.
- The context contains a representation of the transaction.

The logic of the validator script is then: does the transaction make a payment from the second party to the first party, containing the value that they are supposed to send? 
If so, then they may spend this output and send it where they want (or we could insist that they send it to their key, but we might as well let them do what they like with it).

## Different kinds of scripts

The Cardano ledger currently has a few different kinds of validator scripts:

- The "simple" script language (introduced in the Allegra hard fork), which allows basic checks such as time locks
- Various Plutus language versions (see `What are Plutus language versions? <what_are_plutus_language_versions>`{.interpreted-text role="ref"})

## Further reading

See [The EUTXO Handbook, A deep dive into Cardano's accounting model](https://www.essentialcardano.io/article/the-eutxo-handbook).

The Extended UTXO Model is described in :cite[functional-smart-contracts-summit]{.title-ref}. 
More formal detail can be found in in :cite[eutxo,utxoma,eutxoma]{.title-ref}.

For more help on how to actually implement interesting logic using the EUTXO model and scripts, read some of our `tutorials<plutus_tutorials>`{.interpreted-text role="ref"}.

# Plutus Foundation

In order for an application to run its `trusted kernel<what_is_the_plutus_platform>`{.interpreted-text role="ref"} of logic as a script on a `ledger<what_is_a_ledger>`{.interpreted-text role="ref"}, the ledger needs a way of specifying and executing scripts. 
Scripts are simply programs, so this means we need a *programming language*.

## Plutus Core

In the Plutus Platform, this language is *Plutus Core*. 
Plutus Core is a variant of the lambda calculus, a well-studied formalism for computing.

> **Note**
> 
> Plutus Core is our "assembly language". Trust me, you don't want to see any! Dealing with that is the compiler's job.

Plutus Core is designed for simplicity, determinism, and to allow careful cost control of program execution. 
Using the lambda calculus makes it an easy compilation target for functional programming languages, and allows us to have a simple, formally verified evaluator.

## Plutus Tx

Writing Plutus Core by hand is not a job for a human! 
It is designed to be written by a compiler, and the Platform provides a compiler from a subset of Haskell to Plutus Core. 
This allows you to seamlessly write applications in Haskell, while compiling part of the code to on-chain Plutus Core, and part into an off-chain application.

Supporting "mixed" code in this way enables libraries written with the Plutus Haskell SDK to share logic and datatypes across both parts of the application, reducing the risk of errors significantly.

## Further reading

The formal details of Plutus Core are in its specification :cite`plutus-core-spec`{.interpreted-text role="p"}. 
The design is discussed in :cite[plutus-report]{.title-ref}.

For more about Plutus Tx, see the `tutorial<plutus_tx_tutorial>`{.interpreted-text role="ref"}.

# Plutus language versions

The Cardano ledger tags scripts with a *language*. 
This determines what the ledger will do with the script.

For example, the "simple" script language introduced in the Allegra era allows for a few basic kinds of checks to be made, such as time locks. 
In order to interpret simple scripts, the ledger must (among other things) extract the validation interval information from the transaction in order to check the conditions imposed by the script.

Plutus scripts, introduced in the Alonzo era, have a more complex interface than simple scripts. 
Plutus scripts are programs written in the Plutus Core programming language that receive three arguments:

> 1. the datum,
> 2. the redeemer, and
> 3. the context.

The *context* contains all the information about the transaction which is currently being validated. (See `Scripts and the Extended UTXO model <scripts_and_the_eutxo_model>`{.interpreted-text role="ref"} for more details).

Languages must continue to behave the same forever; otherwise, we could change the behaviour of existing scripts, potentially making outputs un-spendable and breaking users' assumptions. 
That means that many kinds of changes to the behaviour of the language instead require a "new" language. 
This includes changes to the interface of the language.

For example, if we want to put more information in the *context* (e.g., in order to convey information about new fields that have been added to transactions), then we need a new language, because old scripts would not be able to understand the new information.

> **Note**
> 
> For more details about what kinds of changes require a new language, see the Cardano Improvement Proposal, [CIP 35\--Plutus Core Evolution](https://cips.cardano.org/cips/cip35/).

Hence, in order to change Plutus, we need to create a new language in the ledger. 
Since in most cases this language will be very similar to the ones that came before, we refer to these as "Plutus language versions." 
However, from the ledger's perspective, they are entirely unrelated and there is generally no requirement that they be similar or compatible in any way.

There are two different uses of "language" here that are important to keep distinct:

> - Plutus Core is a *programming* language in which Plutus scripts are written;
> - Plutus (the Plutus Core programming language and a particular interface) is a "language" in the terminology of the ledger.

In particular, a specific version of the Plutus Core programming language may be used in multiple versions of the Plutus ledger language, if, for example, the only difference is to the interface. 
To date, all versions of Plutus use the same version of the Plutus Core. 
That means that, in practice, the process for creating scripts of different Plutus language versions tends to be similar. 
The main difference is that you will likely need a different `ScriptContext` type, and different
built-in functions may be available.

*See also:*

- `Plutus language changes <plutus_language_changes>`{.interpreted-text role="ref"} for a description of what has changed between versions.
- `Upgrading to Vasil and Plutus script addresses </reference/cardano/upgr-vasil-plutus-script-addresses>`{.interpreted-text role="doc"}.
