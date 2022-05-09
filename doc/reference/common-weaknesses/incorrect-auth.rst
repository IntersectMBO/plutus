Incorrect Authentication
========================

Failure to authenticate the wallet spending a UTXO properly. UTXO validators are often intended to restrict spending to authorized wallets, for example by checking that the spending transaction is signed by the correct wallet(s), or by checking for the presence of an authorization token. 

Risks
~~~~~

Accidentally omitting this check would enable theft of the UTXO, so it is important to ensure this does not happen. 

At the same time, some UTXOs are intended to be spendable by anyone. So it is not necessarily wrong for such checks to be omitted.


Solutions
~~~~~~~~~

Generated test cases can be mutated so that actions intended to be performed by one wallet are performed by another instead. Contract models already tell us what to expect when this is done: if the precondition of the mutated action is false, then it should fail or behave as a no-op, while it the precondition is true, then this is simply an action that can be performed by more than one wallet. Thus this kind of failure can be detected just by mutating test cases as described, and running and evaluating tests with false preconditions.

