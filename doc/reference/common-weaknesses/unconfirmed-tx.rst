Failure to wait for transactions to be confirmed
================================================

Submitting a transaction does not guarantee that it will take effect. The transaction might be erroneous, it might be rejected by one of its inputs, it might not be committed before its deadline, it might not reach the network, it might lose a race to spend a UTXO, it might be rejected by the user, the submitting wallet might contain insufficient funds to balance the transaction, it might be rolled back.

Risks
~~~~~

A contract which does not wait for a transaction to be confirmed cannot know whether it has taken effect or not, which may lead to unintended consequences later. In particular, successive endpoint calls may try to spend the same UTXOs: if the first endpoint call did not wait for its transaction to complete, and the second call looks for unspent UTXOs to use, the the second call is likely to try to spend the same UTXOs as the first, leading its transactions to be rejected. For example, the Vesting example contract (in plutus-use-cases) can submit two “retrieve” transactions that try to spend the same inputs. In this case the off-chain contract assumes transactions will succeed, and may actually terminate “successfully” even though funds remain locked on the chain. 

However, there are conceivable situations in which an off-chain contract might not need to wait for a transaction to be confirmed.


Solutions
~~~~~~~~~

In normal testing, we expect that all submitted transactions will also be confirmed. However, contracts also need to be tested with an arbitrary subset of submitted transactions being discarded instead. In general there will be too many transactions for exhaustive exploration of dropping all subsets to be feasible, but random sampling should be effective at revealing bugs in this area. 

Obviously, dropping transactions may cause the observed behaviour of the contract to change, but it should still be “safe” in some sense. For example, a contract might time out and resubmit failed transactions, to exhibit the same behaviour as without transaction dropping, or it might simply drop them, and ensure that endpoint calls whose transactions are dropped behave as a no-op. The challenge here is to make “safe” precise, ideally reusing the same contract model, perhaps with minimal extensions to specify new possible behaviours.

