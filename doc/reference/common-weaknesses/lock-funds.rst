Contracts may potentially lock funds forever
============================================

This may happen directly, through the creation of a UTXO containing funds which can never be spent because the validator always rejects transactions. It may also happen indirectly, because the contract places funds in a UTXO which can only be spent by a transaction placing the funds in another, similar UTXO—thus allowing any number of transactions to take place, but preventing the funds from ever reaching an external wallet.

Risks
~~~~~

Even if funds can always be recovered from a contract, this may require cooperation from malicious parties, who can choose simply not to assist in recovering the funds.

Solutions
~~~~~~~~~

Developers should provide strategies that can be used to recover funds. One strategy, the “no locked funds” strategy, demonstrates simply that funds can always be recovered into wallets. A second more refined strategy demonstrates that every beneficiary wallet can recover its share of the contract’s funds without help from other wallets (which will probably require waiting for time limits to expire in most cases). The contract model framework already supports defining and testing such strategies; we expect them to be used to address other problems also. Since every UTXO must contain a positive amount of Ada, then passing the “no locked funds” property also guarantees that a contract does not leave any unspent script UTXOs after its execution. To satisfy this property, even a contract that is intended to run indefinitely must nevertheless provide a controlled way of shutting it down, because that is the only way to recover all of the locked funds.

