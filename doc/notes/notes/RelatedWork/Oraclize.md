# Oraclize

* [Website](http://www.oraclize.it)
* [Protocol specification](http://docs.oraclize.it/)
* [GitHub](http://github.com/oraclize)
* Integrated with Ethereum, Rootstock, Corda, and looking at supporting Bitcoin directly.


## Purpose

Acts as a data carrier that enables smart contracts isolated in a VM to access external information in a manner that conveys trust about the supplied information. In particular, Oraclize can query IPFS or arbitrary https endpoints. These queries can be timed, for example, to realise updates at regular intervals (such as needed for a stock ticker). 
  
## Evidence

Oraclize uses TLSNotary as well as their own work on tamper-free Android apps and a French hardware wallet vendor to supply evidence that the supplied information is from a trusted source and has not been tampered with. Due to their size (and the associated costs), these proofs are typically not communicated to the smart contract directly, but committed to IPFS, where Oraclize ensures persistence of the information by way of the work of the IPFS persistence consortium. 

This appears to create a situation, where validation is inherently relying on off-chain resources and processing.