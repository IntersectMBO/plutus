---
title: Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G1.Arith
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381-cardano-crypto-tests/G1/arith`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G1.Arith where

open import Conformance.Eval
```

## add

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G1/arith/add
-- Check that adding two random points in G1 gives the expected result.
test-add : Untyped
test-add = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\185\&1\ENQ\208\207\244\195\246\164*\183\144\144\n&\187\CANC\244\176\DEL\200=Rzf\228\162\221\246\196\158\168o\227{\DC1\ACK\219\210\r\194\128\236Y\150\218\223"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\160w$gB\191\191\253\239\193\EM:\186\ETBCM3\DEL#\DC4x\191c\ETB0e\193\224\156\&4B\158v\135y\131\174_:\221\DC48\229\210\&7\246\&7$"))))))) (UCon (tagCon bytestring (mkByteString "\152c\235\n\DEL\139\t/\202\SUBC3\134j\227W\154\210\164\237\239\132\191\205\247\&63;:\223\SOH\NUL\130\fv\ETX\176\STX\191\145\ESCVL\240\&29/\a"))))

expected-add : Result
expected-add = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`.
pending-add : Set
pending-add = Pending (evalRaw test-add ≡ expected-add)
```

## neg

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G1/arith/neg
-- Check that negating a random point in G1 gives the expected result.
test-neg : Untyped
test-neg = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-neg) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\185\&1\ENQ\208\207\244\195\246\164*\183\144\144\n&\187\CANC\244\176\DEL\200=Rzf\228\162\221\246\196\158\168o\227{\DC1\ACK\219\210\r\194\128\236Y\150\218\223"))))))) (UCon (tagCon bytestring (mkByteString "\153\&1\ENQ\208\207\244\195\246\164*\183\144\144\n&\187\CANC\244\176\DEL\200=Rzf\228\162\221\246\196\158\168o\227{\DC1\ACK\219\210\r\194\128\236Y\150\218\223"))))

expected-neg : Result
expected-neg = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-neg`; postulated builtin `bls12-381-G1-uncompress`.
pending-neg : Set
pending-neg = Pending (evalRaw test-neg ≡ expected-neg)
```

## scalarMul

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G1/arith/scalarMul
-- Scalar multiplication gives the correct result.
test-scalarMul : Untyped
test-scalarMul = (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-scalarMul) (UCon (tagCon integer (ℤ.pos 29342537169447282925541144552701591957563885683358707334406144036950193508773)))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\160w$gB\191\191\253\239\193\EM:\186\ETBCM3\DEL#\DC4x\191c\ETB0e\193\224\156\&4B\158v\135y\131\174_:\221\DC48\229\210\&7\246\&7$"))))))) (UCon (tagCon bytestring (mkByteString "\160w\150 ,?\202\212\ENQ\165\218X\217\159\SOH\148\200\238!\153\157\208\&2\145\240\191\233~h\235Ni\a|\248\ENQ+\159]\156\188J\DC3\148\186\160\224\216"))))

expected-scalarMul : Result
expected-scalarMul = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-scalarMul`; postulated builtin `bls12-381-G1-uncompress`.
pending-scalarMul : Set
pending-scalarMul = Pending (evalRaw test-scalarMul ≡ expected-scalarMul)
```
