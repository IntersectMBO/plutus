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
test-off-curve = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "864cc4f64b12ca99ecdd1962572e6add609d9c619aab678b3fc298bc2f0f81feb4f0d3ebad7e850a8bcb52ca467e649d"))))

expected-off-curve : Result
expected-off-curve = failure

-- Pending: postulated builtin `bls12-381-G1-uncompress`.
pending-off-curve : Set
pending-off-curve = Pending (evalRaw test-off-curve ≡ expected-off-curve)
```

## out-of-group

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G1/uncompress/out-of-group
-- This contains a value which is the x-coordinate of a point which lies on the
-- E1 curve but not the G1 subgroup.
test-out-of-group : Untyped
test-out-of-group = (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "9483141c933166b61990a706aca07f467d22bc34c6552f5bba91cb1fc21db51d03dfff6523a5e1b4285d54c47660eda1"))))

expected-out-of-group : Result
expected-out-of-group = failure

-- Pending: postulated builtin `bls12-381-G1-uncompress`.
pending-out-of-group : Set
pending-out-of-group = Pending (evalRaw test-out-of-group ≡ expected-out-of-group)
```
