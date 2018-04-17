# Syntax of Version Identifiers in Similar Systems

Blockchain systems are the only place I'm seeing this done. In my experience this sort of version management is offloaded to other software systems (package managers and their lookalikes, including `make` and `nix`). I suppose this makes sense.

Solidity and Liquidity embody the two sides of a design tradeoff. With Solidity, source files may (and really, should) specify a version range, and compilers will refuse to compile the code if they are outside of the range. With Liquidity, source files specify a version of the language, and a compiler will accept the code if and only if it supports that version.

The approach in Liquidity strikes me as being a lot friendlier to the programmer, and I propose we adopt their scheme (compiler decides) and syntax.

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

Exapmle contracts include a Solidity version pragma. (see [examples](https://github.com/qtumproject/solar/tree/master/contracts)).

