Inconsistent time-outs and transaction validity intervals
=========================================================

Once a transaction is submitted, it could be added to the blockchain at any time up until the end of its validity interval. Off-chain code that needs to observe whether the transaction succeeded or not must wait until the validity interval has expired to be sure that the transaction has failed.

Risks
~~~~~

Off-chain code which waits too short a time may take action on the assumption that the transaction failed, only for it to take effect later, which may result in incorrect behavior overall. Transaction validity intervals in the validators on-chain and time-outs in the off-chain code need to correspond, or there may be a risk of errors.

Solutions
~~~~~~~~~

Timeouts and transaction validity intervals need not correspond exactly, provided the offchain code handles transactions that take effect after timeouts correctly. To establish this, testing must include cases in which transactions are delayed until after relevant timeouts have occurred. This will require extensions to the emulator, which at present commits transactions as soon as they are submitted.

