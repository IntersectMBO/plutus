---
title: Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G1.Uncompress
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381-cardano-crypto-tests/G1/uncompress`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381CardanoCryptoTests.G1.Uncompress where

open import Conformance.Eval
```

## off-curve

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G1/uncompress/off-curve
-- This contains a value which is not the x-coordinate of a point on the E1 curve.
test-off-curve : Untyped
test-off-curve = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\134L\196\246K\DC2\202\153\236\221\EMbW.j\221`\157\156a\154\171g\139?\194\152\188/\SI\129\254\180\240\211\235\173~\133\n\139\203R\202F~d\157"))))

expected-off-curve : Result
expected-off-curve = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-uncompress`.
pending-off-curve : Set
pending-off-curve = Pending (evalRaw test-off-curve ≡ expected-off-curve)
```

## out-of-group

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G1/uncompress/out-of-group
-- This contains a value which is the x-coordinate of a point which lies on the
-- E1 curve but not the G1 subgroup.
test-out-of-group : Untyped
test-out-of-group = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "\148\131\DC4\FS\147\&1f\182\EM\144\167\ACK\172\160\DELF}\"\188\&4\198U/[\186\145\203\US\194\GS\181\GS\ETX\223\255e#\165\225\180(]T\196v`\237\161"))))

expected-out-of-group : Result
expected-out-of-group = failure

-- Pending: bytestring constant; postulated builtin `bls12-381-G1-uncompress`.
pending-out-of-group : Set
pending-out-of-group = Pending (evalRaw test-out-of-group ≡ expected-out-of-group)
```
