# Echidna

* [Blog post](https://blog.trailofbits.com/2018/05/03/state-machine-testing-with-echidna/)
* [GitHub](https://github.com/trailofbits/echidna)

*Echidna* is a Haskell library for property-based testing of Solidity smart contracts on the basis of a state machine model of the contract. It uses Hedgehog as its testing framework. Based on the state-machine model, the library supports writing *commands* that perform state transitions and *properties* that assert invariants. The latter involve randomly generating sequences of commands, executing them in the EVM, and checking that the resulting EVM state matches that of the Haskell model.