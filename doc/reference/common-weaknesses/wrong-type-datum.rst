Wrongly typed UTXO datum or redeemer
====================================

Validator scripts are usually written in a typed form, in which the types of the corresponding datum and redeemer are specified. But since both are provided using a universal “Data” type, then it is possible to supply the wrong type of data, either when creating a UTXO, or when trying to redeem one. The “typed script” API provided helps to protect against such errors, but does not exclude them altogether.

Supplying a redeemer of the wrong type for a UTXO will cause the validation script to reject the transaction, because converting the redeemer to a correctly typed argument will encounter an exception. 

Risks
~~~~~

Creating a UTXO with a datum of the wrong type for its validator script may succeed, but such a UTXO can never be spent, because calling the validator will always raise an exception as it tries to decode the datum. 

Solutions
~~~~~~~~~

testing the “no locked funds” property (see point 30) ensures that any unspendable UTXOs cannot be holding funds. Since all UTXOs must hold a minimum amount of Ada, then this also guarantees that no unspendable UTXOs are created, and so no UTXOs can have an ill-typed datum.

Since a wrongly typed redeemer will always cause a transaction to fail, then it can be detected by checking that every transaction in the source code succeeds at least once during testing.

