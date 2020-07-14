# Counterparty

* [Website](https://counterparty.io)
* [Protocol specification](https://counterparty.io/docs/protocol_specification/)
* [GitHub](https://github.com/CounterpartyXCP)
* Implemented on top of Bitcoin
* Integration of Solidity contracts 
* Status: as of April 2018, operational, but seemingly without smart contracts


## Integration with Bitcoin

* Encodes custom data in Bitcoin outputs by using two out of three addresses in a multsig output and by using OP_RETURN.
* That custom data is used to encode the following types of operations executed on an off-chain account-based ledger:
  * Creating custom assets
  * Sending custom assets (and Bitcoin) from one account to another
  * Filling an order book with orders
  * Betting on information feeds also encoded by Counterparty
  * Paying of dividends
  * Smart contract deployment and execution
  
## Ethereum support by Counterparty

They integrate the execution of Ethereum contracts in Solidity by encoding operations in Bitcoin transactions that correspond to creating an Ethereum contract and to an external call into an existing Ethereum contract. In both cases, whenever a Counterparty node sees such a transaction, it waits until it is sufficiently confirmed and then executes the corresponding operations in its attached (and somewhat modified) EVM. All state of Ethereum contracts is kept in a database in the nodes (it is not committed to the blockchain). Moreover, XCP (Counterparty token) and custom assets can be sent to contracts to fund them. 