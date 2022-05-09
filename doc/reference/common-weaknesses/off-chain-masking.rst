On-chain checks may be masked by off-chain checks
=================================================

UTXO validators make checks on transactions before allowing coins to be spent. These checks are performed on-chain, but often are also duplicated off-chain or in the wallet before a transaction is submitted. If the off-chain code duplicates checking performed by validators such that invalid transactions are not submitted to the block chain it is possible that testing coverage may be incomplete.

Risks
~~~~~

The consequence of off-chain code performing these checks, though, is that the on-chain checks may never fail during testing—and thus, if the on-chain checks are too liberal, or omitted entirely—then testing may not reveal that.

Solutions
~~~~~~~~~

To exercise the checks in the on-chain code, it is necessary to run tests in which transactions are generated and submitted without going through the off-chain code. It’s possible that the off-chain code can be structured in such a way that this is eased.

