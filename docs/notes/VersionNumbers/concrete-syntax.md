# Syntax of Version Identifiers in Similar Systems

## Solidity (Ethereum)

The [version pragma](http://solidity.readthedocs.io/en/v0.4.22/layout-of-source-files.html?) is optional but reccommended. For example:
```
pragma solidity ^0.4.0;
```
ensures that a program will not compile with a compiler earlier than version 0.4.0, or with any compiler from version 0.5.0 (which is the meaning of the `^`). The documentation claims it is possible to specify more complex version identifiers using the [npm](https://docs.npmjs.com/misc/semver) scheme.

## Liquidity (Tezos)

The [version statement](https://github.com/OCamlPro/liquidity/blob/next/docs/liquidity.md) is mandatory, and the compiler will reject any contract with a version it cannot compile. (Compare to the situation with Solidity, where the code specifies which compiler versions are acceptable). The syntax is:
```
[%%version 0.14]
```

## Sophia (Aeternity)

The [documentation](https://github.com/aeternity/protocol/blob/master/contracts/sophia.md) makes no mention of version identifiers and the example (which is emphatically not production code) does not contain one, so no syntax for us to compare here.

## Solar (Qtum)

Contracts include a Solidity version pragma. (see [examples](https://github.com/qtumproject/solar/tree/master/contracts)).

