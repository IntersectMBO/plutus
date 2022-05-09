Size limits may prevent transactions succeeding, and prevent recovery of funds
==============================================================================

There are size limits on the number of different tokens in a UTXO, and on the sizes of transactions as a whole. If these limits are exceeded, then the offending transaction will be rejected. That some transactions are rejected, instead of storing too much information on the blockchain, is not necessarily a problem.

Risks
~~~~~

If it is possible to reach a state such that the only way to recover the funds in the contract requires transactions that exceed the size limit, then the funds may become irretrievable.

Solutions
~~~~~~~~~

Testing the “no locked funds” property addresses this problem in principle, but to be effective we need to test cases in which the transactions approach, and sometimes exceed, the maximum permissible size. This will require custom test case generation, which deliberately builds large transactions and UTXOs.

