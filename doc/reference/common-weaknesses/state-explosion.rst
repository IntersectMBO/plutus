State-space explosion due to unconfirmed transactions
=====================================================

When a contract submits a set of independent transactions, any subset might eventually be confirmed, potentially resulting in an explosion of possible blockchain states.

Risks
~~~~~

Contracts that submit an unbounded number of transactions, without waiting to be sure they are confirmed, may simply be infeasible to test thoroughly—or to understand—because the state space is so large.

Solutions
~~~~~~~~~

Contract developers should wait for transactions in flight to be confirmed, or expire, at appropriate points. Contract models might impose an upper limit on the number of simultaneous transactions in flight, to ensure that the state space does not grow unreasonably large.

