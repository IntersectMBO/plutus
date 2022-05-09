Execution cost limits may prevent recovery of funds
===================================================

Cardano places fixed limits on the execution cost of each script. It may be possible for a sequence of operations to put the contract into a state in which no withdrawal is possible, because of execution cost limits.

Risks
~~~~~

If a sequence of transactions increases the size of the datum in a contract’s UTXOs, then eventually the UTXOs may become unspendable, because running the associated script will always exceed the blockchain’s execution cost limit. This kind of problem is quite tricky to test for, because UTXOs created during normal tests are unlikely to approach the size of datum needed to provoke the failures.

Solutions
~~~~~~~~~

We could track the execution costs of scripts during testing, and require that every script invocation in a transaction submitted by a fund recovery strategy should cost less than the maximum script execution cost before fund recovery started. This would show that, if we can reach the state from which fund recovery starts, then we will also be able to complete the recovery. 

Meeting this requirement could force developers to precompute information needed for recovery during the earlier transactions, or to break the fund recovery into many small transactions with low-cost scripts. In either case, these measures would indeed help to solve the real problem. Although we would be testing these properties on relatively small data (and so, probably, very far from the actual cost limits), establishing that recovering funds is no more expensive than other operations for small data would increase confidence that the same is true for large data. It would be advisable to run some tests with large data too, running close to the actual limits expected on the blockchain, in case withdrawal operations have a higher complexity (but lower constant factors) than others.


