# Support for Floating Point Numbers in Smart Contract Systems

In summary, the purpose-built languages do not support floating point numbers. 

## Solidity

Plans to support [fixed point numbers](http://solidity.readthedocs.io/en/develop/types.html?highlight=float#fixed-point-numbers), but doesn't seem to yet.

## Liquidity

Liquiditiy [does not](https://github.com/OCamlPro/liquidity/blob/next/docs/liquidity.md) have built in floating point numbers.

## Bitcoin Script

Bitcoin script [does not](https://en.bitcoin.it/wiki/Script#Arithmetic) support floating point numbers.

## Sophia

Aeternity's Sophia [does not](https://github.com/aeternity/protocol/blob/master/contracts/sophia.md#types) support floating point numbers.

## EOS

EOS provides support for WebAssembly, which supports multiple languages with floating point numbers.

## NEO

NeoVM promises to support .NET and JVM languages, many of which include support for floating point numbers.

## Qtum

Is able to run both EVM byte code and bitcoin script, so presumably one has access to fixed point numbers through Solidity, but not floating point numbers.

