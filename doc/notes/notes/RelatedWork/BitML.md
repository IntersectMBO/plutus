# BitML

* [Paper](https://eprint.iacr.org/2018/122.pdf)

*BitML* is a domain-specific language for smart contracts compiled to Bitcoin script. It is defined as a process calculus that is sufficiently expressive to cover most applications proposed in the literature for Bitcoin script, including escrow services, timed commitments, and multi-player lotteries. The DSL comes with a symbolic semantics. The paper also defines a computational model and establishes a relationship between the symbolic semantics and the computational model, which they call *coherence*. Based on this notion of coherence, the paper establishes the soundness of the compiler that takes the DSL into Bitcoin script.

BitML supports stipulating contracts, where all involved participants have to agree before the contract is active on the blockchain. Moreover, there is language support for managing deposits, secrets, splitting funds, waiting for authorisation, and time-dependent clauses.