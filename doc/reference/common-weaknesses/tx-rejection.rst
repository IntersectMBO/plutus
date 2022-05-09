Failure to test transaction rejection
=====================================

Any transaction submitted by off-chain code may be rejected, despite being perfectly valid. The wallet balancing the transaction may run out of funds, the wallet owner may simply decide not to sign the transaction, a competing transaction may spend one of the transaction’s inputs first, or the transaction may simply fail to be confirmed before its validity interval expires. Contracts need to be written to respond sensibly to this.

Risks
~~~~~

Any code relying on an assumption that the transaction will be processed without verifying that the transaction is on chain and not subject to being rolled back is at risk of causing an action to be performed without the triggering transaction having happened.


Solutions
~~~~~~~~~

Contracts’ behavior needs to be tested when subsets of transactions are discarded, as well as when all valid transactions are confirmed. In principle any subset of submitted transactions might be discarded, although transaction dependencies may mean that discarding one transaction also effectively discards others. In long tests, then repeating the test while discarding every subset of transactions would be infeasible (because there are exponentially many subsets), but discarding random subsets should suffice to find bugs. Contract models also need to be written so as to validate the contract’s behavior when some transactions are discarded, since it is likely to differ from the behavior when all transactions succeed.

