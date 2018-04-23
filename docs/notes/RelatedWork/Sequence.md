# Tezos

* [Website](http://tezos.com)
* [White paper](https://www.tezos.com/static/papers/white_paper.pdf)
* Account-based ledger
* Smart contracts are associated with persistent storage whose structure is part of the smart contract definition.

## Michelson

[Michelson](https://www.michelson-lang.com) is the native smart contract language of Tezos. It is a strongly-typed, stack-based language with a [formal specification](https://www.tezos.com/static/papers/language.pdf).

See also [Phil's evaluation](https://wadler.blogspot.com.au/2017/12/simplicity-and-michelson.html).

## Liquidity

Liquidity is functional, statically and strongly typed language that compiles down to Michelson. Syntactically, it is a subset of OCaml with a [formally specified compilation scheme](http://www.ocamlpro.com/2018/02/08/liquidity-smart-contract-deploy-live-demo-on-tezos-alphanet-jfla2018/#compilation-schema) producing Michelson. More details are in a [blog post](http://www.ocamlpro.com/2018/02/08/liquidity-smart-contract-deploy-live-demo-on-tezos-alphanet-jfla2018/) and examples are in the [GitHub repo](https://github.com/OCamlPro/liquidity/tree/master/tests/others).

Liquidity places strong emphasis on easy decompilation with the aim to simplify the inspection and validation of contract deployed to the blockchain in Michelson, but generated from a high-level Liquidity program. To be honest, I don't quite see the importance of that, given we can use hash-based schemes to tie sources and bytecode together as is routinely done by Solidity on Ethereum.
