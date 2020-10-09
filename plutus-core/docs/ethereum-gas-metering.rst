Notes on Ethereum Gas Metering
==============================

Intro
-----

Ethereum assigns a cost (called gas) to each EVM low-level operation
(opcode); the gas is an abstract unit to measure “how computationally
expensive” is an EVM operation. The reason for having gas costs is to
charge the Ethereum users for running their contracts inside the
Ethereum node-machines, proportionally to the total gas
(i.e. utilization of a node machine) for each contract.

The Ethereum miners (nodes) are compensated by Ether with value:
``(gas_total * gas_price_in_ether)`` for each executed contract. Since
Ether is volatile, but miners’ electricity-costs/hardware costs are
priced on more stable currency, the ``gas_price`` is a *dynamic* value
supplied for each contract; nodes can delay or reject executing
unattractive contracts — with low payoff taking into account the
``gas_price`` and ethereum exchange rates — . Users, on the other hand,
can prioritize their contracts for execution by raising their contracts’
``gas_price``.

There is a user-specified “gas-limit” per transaction; the contract
execution will halt if it exceeds limit, but if it finishes sooner the
gas-remainder will be refunded to the user. There are 2 reasons for
having a gas-limit:

1. the user commits upfront with ``gas_limit*gas_price`` ether amount
   and thus the node can be assured up to this amount for its
   compensation.
2. the total gas cost for a given contract cannot always be precisely
   calculated before its inclusion in a block, since contracts depend on
   the current blockchain state. To safeguard against runaway/expensive
   computations, the user can specify an expected hard upper limit.

Initially, the Ethereum developers, through benchmarking (on unspecified
hardware), have determined the gas cost (positive natural {1,2,3,…}) for
each operation. Gas costs are generally a fixed value, but there are
some EVM operations that vary their gas cost proportionally to the
“size” of their operand(s).

Miscalculations of Ethereum costs
---------------------------------

Lies, damned lies and benchmarks
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Benchmarking is difficult to get right, because:

a. filtering out the “noise” from the benchmark results is hard (i.e not
   capturing measurements that are irrelevant to the thing we try to
   benchmark)
b. the benchmarks are run on a certain, given environment (setup), which
   is not universal and thus not reproducible.

As such, the initial benchmarks of Ethereum turned out to have some
miscalculations for certain EVM opcodes, and Ethereum responded by
adjusting their costs through various EIPs.

Hardware changes
~~~~~~~~~~~~~~~~

Hardware keeps advancing and the ``CPU vs MEM vs IO speed`` may change
in the future, which means that gas costs may as well need to be
adjusted accordingly, since opcodes vary among each other for their
dependence on CPU / MEM / IO. Related to this, is that not every node
can be expected (or even controlled) to run the same hardware, and costs
in general differ among hardware architectures.

Software changes
~~~~~~~~~~~~~~~~

Software and OS change because of better implementations
(geth,parity,aleth nodes), or by reacting to newer hardware, or more
fundamentally by having cleverer ways to solve problems (e.g. a better
algorithm for hashing). As such the gas costs may need to be adjusted
accordingly.

A growing Ethereum state
~~~~~~~~~~~~~~~~~~~~~~~~

The Ethereum state can be imagined as a huge database that stores
account balances and contract state. The size is in general
ever-growing, both because of more Ethereum accounts being created, but
more importantly because of contracts storing more state.

Some of the EVM opcodes read from or write to this state database. If we
assume that the database keeps growing while the hardware stays the
same, such I/O opcodes are becoming over time more and more expensive to
execute proportionally to the other opcodes. Even with newer hardware,
it would require that the I/O hardware advancements are outpacing
CPU/other hardware advancements by a factor of the state’s growth-rate —
highly unlikely — to expect no future adjustments to the gas costs.
Ethereum has made several adjustments to such I/O opcodes that were
considered under-priced through various EIPs over the years.

Baird et al. (2019) proposes a fix with a new cost-model where some
I/O-intensive opcodes increase their gast cost proportionally to the
current blockchain height.

The role of the system cache
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Although not as important as other types of miscalculation, the cache
plays somewhat a role in determining the “real” computational cost of
the EVM operation. Given a specific blockchain version and generation,
there is a “cost-model” (assigning gas costs to opcodes) precisely
defined and agreed among the participants, so as to make the
metering/accounting deterministic among the distributed system. However,
the real computational costs are never fixed; they depend on the current
“state-of-operation” of the mining machine (even if we pin all the
mining-node machines down to the same hardware/software/OS). This
“state-of-operation” refers to the “cache” of the system, which
introduces variance to the real computational costs of the EVM opcodes;
there can be instance where the exact same EVM operations may run faster
or slower, depending on what the cache of the node-machine currently
contains. For this reason, the cost model is considered to be an
“average” among this variance. Ignoring the fact that the cost model is
cache-oblivious and thus slightly inaccurate, this can theoretically
pose an issue if a malicious user can craft special, cache-polluting
contracts so as to trigger a DoS attack (see DoS attacks below). Yang et
al. (2019) studies the effect of cache on Ethereum gas costs.

It is interesting what role the cache will play for Plutus; since Plutus
contracts are stateless and can be generally re-used, it may be that
certain contracts are way more popular (executed more often) than
others. This means that such smart-contracts will in reality be way
cheaper to execute than others with same gas costs, because their
popularity made their code more likely to exist already in cache.

Why miscalculations are bad?
----------------------------

DoS attacks
~~~~~~~~~~~

A malicious user could start a Denial-of-Service attack to the network
by issuing smart-contracts containing under-priced operations that are
computationally expensive. This can lead to lowering the overall
transaction throughput of the blockchain system, but assuming a correct
implementation of the distributed system, will not be catastrophic to
the operation of the whole blockchain. Such DoS attacks have previously
happened to Ethereum, which made the system way slower than the average
of 15s to mine a block (validate a transaction), and has been fixed by
the introduction of EIP150. The malicious user may be incentivized by
being a currency/blockchain/system competitor or by having an interest
in shorting. Perez and Livshits (2020) investigate the generation of
“under-priced” smart contracts through genetic programming to trigger
DoS attacks to Ethereum.

Trust to the blockchain system
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Fairness of execution is a sought-after feature and contributes to the
overall trust of the whole blockchain system. If some computations are
overpriced or impossible to execute it can drive users away from
participating in the system (by submitting smart-contract transactions).
On the other hand, nodes will be less inclined or even deny to execute
contracts containing (many) under-priced operations.

Why adjusting the cost-model is bad?
------------------------------------

First to be clear, adjusting the cost-model during the lifetime of a
smart-contract blockchain is perhaps *inevitable*.

However, continuously adjusting the cost model can lead to problems,
such as:

-  Established contracts that were previously working just fine, can now
   be unrunnable because their total gas-costs have been increased to
   exceed the user’s gas-limit or blocks gas-limit.
-  Adjusting the cost-model may require a hard fork, which is to be
   avoided.
-  In general, adjustments are applied ad-hoc by modifying some
   operations’ costs while keeping other operations’ costs the same.
   However, the gas unit is an integral value which means that some
   ratios/adjustments cannot be applied ad-hoc, and would require a cost
   re-adjustment of all operations.

References
==========

.. container:: references hanging-indent
   :name: refs

   .. container::
      :name: ref-baird2019economics

      Baird, Kirk, Seongho Jeong, Yeonsoo Kim, Bernd Burgstaller, and
      Bernhard Scholz. 2019. “The Economics of Smart Contracts.”
      http://arxiv.org/abs/1910.11143.

   .. container::
      :name: ref-perez2020broken

      Perez, Daniel, and Benjamin Livshits. 2020. “Broken Metre:
      Attacking Resource Metering in Evm.”
      http://arxiv.org/abs/1909.07220.

   .. container::
      :name: ref-yang2019empirically

      Yang, Renlord, Toby Murray, Paul Rimba, and Udaya Parampalli.
      2019. “Empirically Analyzing Ethereum’s Gas Mechanism.”
      http://arxiv.org/abs/1905.00553.
