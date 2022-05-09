Separate contract instances may be confused
===========================================

In the EUTxO model contracts may have multiple instances in operation simultaniously. A contract instance is identified by a specific UTxO carrying the instance state token. Contracts that are designed to have multiple instances must be careful to not allow confusion of the contract inputs, outputs and state belonging to different instances.

When there are a number of on-chain contract instances operating there must be unique identifiers that ensure that inputs, outputs and state tokens are correctly matched to the same contract instance.

Risks
~~~~~

Multiple contract instances could get their state confused leading to loss of funds, permanently locked funds or incorrect transfers. Since anyone can submit transactions based on the UTxOs on chain, an attacker could mix UTxOs from different contract instances to cause incorrect behavior.

Solutions
~~~~~~~~~

Contracts must be designed carefully to ensure that mixing UTxOs from different transactions can never result in a valid transaction. It is important to test multiple instances of the same contract on the blockchain at the same time, interleaving their actions; each instance should separately behave according to the intended behavior of the contract model.

