# Waves Platform

* [Website](https://wavesplatform.com/company)
* [White paper](https://s3.ca-central-1.amazonaws.com/wavesdb.com/images/whitepaper_v0.pdf)
* [GitHub](https://github.com/wavesplatform)
* UTxO ledger? (need to confirm)
* Smart contracts: promised as part of future work
* Status: as of April 2018, running mainnet


## The blockchain architecture

* Leased proof-of-stake, but they are also talking about Bitcoin-NG-like PoW, which they call Waves-NG, and being based on Scorex.
* New custom assets can be created without smart contracts (using special transactions).
* Miners can be incentivised to mine transactions of custom assets by paying them with custom assets, which a simultaneously issued transactions converts before the main transaction can be confirmed. 
* A distributed exchange (DEX) on each core node enables trades between all asset types.
* Core nodes expose a REST API to query the ledger, create transactions, and interact with the DEX.
* The use lightweight nodes that download no blocks (implemented in Javascript as browser plugins), but trust core nodes.
* Implemented in Scala
