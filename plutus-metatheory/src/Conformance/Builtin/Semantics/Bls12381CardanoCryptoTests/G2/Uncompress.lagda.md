---
title: Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G2.Uncompress
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381-cardano-crypto-tests/G2/uncompress`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G2.Uncompress where

open import Conformance.Eval
```

## off-curve

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G2/uncompress/off-curve
-- This contains a value which is not the x-coordinate of a point on the E2 curve.
test-off-curve : Untyped
test-off-curve = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\135\134\CAN9\230\STX\252]\250\r\vr#-\216\GS+\SOKf\n~\186\&5=\162~f\206\175-lw4\146RG(\CANf\161-gu*\RS\218\173\SOH\234Y\228\232n.\133\168\SUBW<\214\143m\251ReX\216\SUB\143H\143&\US5]\218\194?l\175\a\210\DEL\218q\216\243\150\141L\238\218\137\160\157"))))

expected-off-curve : Result
expected-off-curve = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-uncompress`.
pending-off-curve : Set
pending-off-curve = Pending (evalRaw test-off-curve ≡ expected-off-curve)
```

## out-of-group

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G2/uncompress/out-of-group
-- This contains a value which is the x-coordinate of a point which lies on the
-- E2 curve but not the G2 subgroup.
test-out-of-group : Untyped
test-out-of-group = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "\139\216\&6\153\246\aA$H\210\STX\217H\187\DC1\ESC\173\212V\214\128\134\255\154Y\ACK\234;,\218A\DC1\211c\131\145\247\167\177S\238\167z\180r\NAK\214\254\DC3\179P\245\159\136Ln1\172\br9\217\DC4[\129d$\203\162\200\188\183\179\237~\EMc\128\137\217\RS\\\145\&6\210\174\252\141\161e(KB\"\154p"))))

expected-out-of-group : Result
expected-out-of-group = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G2-uncompress`.
pending-out-of-group : Set
pending-out-of-group = Pending (evalRaw test-out-of-group ≡ expected-out-of-group)
```
