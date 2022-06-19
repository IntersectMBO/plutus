Hard limits
===========

Many resources on Cardano are limited in some fashion. At a high level, limits can be enforced in two ways:

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

Risks
~~~~~

This is typically an issue for applications that work with user-supplied data, or data that can grow in an unbounded way over time.
This can result in data which itself becomes large, or which requires a large amount of resources to process.

For example:

- Managing an arbitrary collection of assets (unbounded over time).
- Allowing user-specified payloads in datums (user-supplied unbounded data).

Script size should not itself be a risk (since scripts and their sizes should generally be known ahead of time), but large scripts can reduce the amount of space available for other uses, heightening the risk of hitting a limit.

Solutions
~~~~~~~~~

In the long run, hard limits may be increased, removed, or turned into soft limits.

In the mean time, there are some approaches that developers can use to reduce the risk.

Careful testing
---------------

It is important to test as many of the execution paths of your application as possible.
This is important for correctness, but also to ensure that there are not unexpected cases where script resource usage spikes.

Bounding data usage
-------------------

Carefully consider whether your application may rely on unbounded data, and try to avoid that.
For example, if your application needs to manage a large quantity of assets, try to split them across multiple UTXOs instead of relying on a single UTXO to hold them all.

Providing datums when creating outputs
--------------------------------------

Datum size issues are most likely to be discovered when an output is spent, because the datum is provided only as a hash on the output.
Insisting that the datum is provided in the transaction that creates the output can reveal that it is too big earlier in the process, allowing another path to be taken.
Depending on the application, this may still prevent it from progressing, if there is only one way to move forwards.

If `CIP-32 <https://cips.cardano.org/cips/cip32/>`_ is implemented, this can be done conveniently by using inline datums, although that also risks hitting the output size limit.

Reducing script size costs through reference inputs
---------------------------------------------------

If `CIP-33 <https://cips.cardano.org/cips/cip33/>`_ is implemented, then the contribution of scripts to transaction size can be massively reduced by using a reference script instead of including the entire script.
