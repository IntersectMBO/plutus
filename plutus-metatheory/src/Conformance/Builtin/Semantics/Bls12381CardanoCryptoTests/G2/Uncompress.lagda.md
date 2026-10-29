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
test-off-curve = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "87861839e602fc5dfa0d0b72232dd81d2b0e4b660a7eba353da27e66ceaf2d6c7734925247281866a12d67752a1edaad01ea59e4e86e2e85a81a573cd68f6dfb526558d81a8f488f261f355ddac23f6caf07d27fda71d8f3968d4ceeda89a09d"))))

expected-off-curve : Result
expected-off-curve = failure

-- Pending: postulated builtin `bls12-381-G2-uncompress`.
pending-off-curve : Set
pending-off-curve = Pending (evalRaw test-off-curve ≡ expected-off-curve)
```

## out-of-group

```
-- builtin/semantics/bls12_381-cardano-crypto-tests/G2/uncompress/out-of-group
-- This contains a value which is the x-coordinate of a point which lies on the
-- E2 curve but not the G2 subgroup.
test-out-of-group : Untyped
test-out-of-group = (UApp (UBuiltin bls12-381-G2-uncompress) (UCon (tagCon bytestring (mkByteString "8bd83699f607412448d202d948bb111badd456d68086ff9a5906ea3b2cda4111d3638391f7a7b153eea77ab47215d6fe13b350f59f884c6e31ac087239d9145b816424cba2c8bcb7b3ed7e19638089d91e5c9136d2aefc8da165284b42229a70"))))

expected-out-of-group : Result
expected-out-of-group = failure

-- Pending: postulated builtin `bls12-381-G2-uncompress`.
pending-out-of-group : Set
pending-out-of-group = Pending (evalRaw test-out-of-group ≡ expected-out-of-group)
```
