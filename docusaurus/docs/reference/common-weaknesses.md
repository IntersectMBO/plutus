---
sidebar_position: 20
---

# Common weaknesses

This section provides a listing of common *weaknesses* in Plutus applications. "Weakness" is used in the sense of the [Common Weakness Enumeration](https://cwe.mitre.org/), as a potential source of vulnerabilities in applications.

## Double satisfaction

Suppose we have a validator V that implements a typical "atomic swap" or "escrowed swap" between A and B where A goes first, i.e. V says:

> This output can only be spent if, in the same transaction, there is an output sending the agreed-upon payment (encoded in the output's datum) to A.

Now suppose that A and B have two swaps in progress, one for a token T1 at the price of 10 Ada, and one for a token T2 at the same price. 
That means that there will exist two outputs, both locked by V.

Now B constructs a transaction which spends both outputs, and creates one output addressed to A with 10 Ada (taking T1 and T2 for himself).

![Double satisfaction](../../static/img/double-satisfaction.png)
_A diagram showing the transaction setup for the double satisfaction of two swaps._

A naive implementation of V will just check that the transaction has *an* output to A with 10 Ada in it, and then be satisfied. 
But this allows B to "double satisfy" the two validators, because they will both see the same output and be satisfied. 
The end result is that B can get away with paying only 10 Ada to A, even though B's true liability to A is 20 Ada.

### What is going wrong here?

It is difficult to say exactly what is going wrong here. 
Neither validator's expectations are explicitly being violated.

One way of looking at it is that this is a consequence of the fact that validators only *validate*, rather than *doing* things. 
In a model like Ethereum's, where smart contracts *make transfers*, then two smart contracts would simply make two transfers, and there would be no problem. 
But in the EUTXO model all a validator can do is try to ascertain whether its wishes have been carried out, which in this case is ambiguous.

Following this metaphor, we can see how the same problem could arise in the real world. 
Suppose that two tax auditors from two different departments come to visit you in turn to see if you've paid your taxes.
You come up with a clever scheme to confuse them. 
Your tax liability to both departments is $10, so you make a single payment to the tax office's bank account for $10. 
When the auditors arrive, you show them your books, containing the payment to the tax office. 
They both leave satisfied.

How do we solve this problem in the real world? 
Well, the two tax offices might have different bank accounts, but more likely they would simply require you to use two different payment references. 
That way, the payment that each auditor expect to see is unique, so they know it's for them. 
We can do something similar in the EUTXO model. 
See the section on [Unique outputs](#unique-outputs) below.

### Risks

This is a serious problem for many kinds of application. 
Any application that makes payments to specific parties needs to ensure that those payments are correctly identified and don't overlap with other payments.

### Solutions

It's possible that a solution will be developed that makes this weakness easier to avoid. 
In the mean time, there are workarounds that developers can use.

- **Unique outputs**

The simplest workaround is to ensure that the outputs which your scripts care about are unique. 
This prevents them being confused with other outputs.

In the swap example, if A had used a different key hashes as their payment addresses in each, then one output could not have satisfied both validators, since each one would want an output addressed to a different key hash.

It is not too difficult to use unique outputs. 
For payments to users, wallets typically already generate unique key hashes for every payment received. 
For payments to script addresses it is a bit more complicated, and applications may wish to include the equivalent of a "payment reference" in the datum to keep things unique.

- **Ban other scripts**

A more draconian workaround is for your script to insist that it runs in a transaction which is running no other scripts, so there is no risk of confusion. 
Note that it is not enough to consider just validator scripts, minting and reward scripts must also be banned.

However, this prevents even benign usage of multiple scripts in one transaction, which stops people from designing interesting interactions, and may force users to break up transactions unnecessarily.

## Hard limits

Many resources on Cardano are limited in some fashion. 
At a high level, limits can be enforced in two ways:

- *Hard limits*: these are limits which cannot be breached. Typically, these are implemented with specific thresholds, where exceeding the threshold causes a hard failure.
- *Soft limits*: these are limits which *can* be breached, but where there is a significant disincentive to do so. One way of implementing a soft limit is to have sharply increasing costs to using the resource beyond the soft limit.

Hard limits are clear, easy to specify, and provide hard guarantees for the protocol, but they have the disadvantage that there is no way to evade the limit. 
This means that there is a discontinuity at the limit: beforehand you can always do more by paying more, but after the limit there is nothing you can do.

Currently, these resources on Cardano have hard limits:

- Transaction size
- Block size
- UTXO size
- Script execution units

If an application *requires* a transaction that exceeds one of these limits, then the application will be stuck unless the limit is increased or removed. 
This is most common when scripts are involved, since a script can require a very particular shape of transaction, regardless of whether this exceeds limits.

Examples:

- A script requires providing a datum which is extremely large and exceeds the transaction size limit.
- A script which locks an output needs more execution units than the limit.
- A script requires creating a single output containing a very large amount of tokens, which exceeds the output size limit.

### Risks

This is typically an issue for applications that work with user-supplied data, or data that can grow in an unbounded way over time. 
This can result in data which itself becomes large, or which requires a large amount of resources to process.

For example:

- Managing an arbitrary collection of assets (unbounded over time).
- Allowing user-specified payloads in datums (user-supplied unbounded data).

Script size should not itself be a risk (since scripts and their sizes should generally be known ahead of time), but large scripts can reduce the amount of space available for other uses, heightening the risk of hitting a limit.

### Solutions

In the long run, hard limits may be increased, removed, or turned into soft limits.

In the mean time, there are some approaches that developers can use to reduce the risk.

- **Careful testing**

It is important to test as many of the execution paths of your application as possible. 
This is important for correctness, but also to ensure that there are not unexpected cases where script resource usage spikes.

- **Bounding data usage**

Carefully consider whether your application may rely on unbounded data, and try to avoid that. 
For example, if your application needs to manage a large quantity of assets, try to split them across multiple UTXOs instead of relying on a single UTXO to hold them all.

- **Providing datums when creating outputs**

Datum size issues are most likely to be discovered when an output is spent, because the datum is provided only as a hash on the output.
Insisting that the datum is provided in the transaction that creates the output can reveal that it is too big earlier in the process, allowing another path to be taken. 
Depending on the application, this may still prevent it from progressing, if there is only one way to move forwards.

If [CIP-32](https://cips.cardano.org/cips/cip32/) is implemented, this can be done conveniently by using inline datums, although that also risks hitting the output size limit.

- **Reducing script size costs through reference inputs**

If [CIP-33](https://cips.cardano.org/cips/cip33/) is implemented, then the contribution of scripts to transaction size can be massively reduced by using a reference script instead of including the entire script.

<!-- Verify that CIP-32 and CIP-33 have already been implemented, and update statements above as appropriate. -->

