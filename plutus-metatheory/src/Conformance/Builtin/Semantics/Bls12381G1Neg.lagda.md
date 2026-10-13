---
title: Conformance.Builtin.Semantics.Bls12381G1Neg
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G1_neg`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G1Neg where

open import Conformance.Eval
```

## add-neg

```
-- builtin/semantics/bls12_381_G1_neg/add-neg
-- Check that adding a random point to its negative gives the zero element.
test-add-neg : Untyped
test-add-neg = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G1-neg) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5")))))))

expected-add-neg : Result
expected-add-neg = success (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`; postulated builtin `bls12-381-G1-neg`.
pending-add-neg : Set
pending-add-neg = Pending (evalRaw test-add-neg ≡ expected-add-neg)
```

## neg

```
-- builtin/semantics/bls12_381_G1_neg/neg
-- Check that negating a random point in G1 gives the expected result.
test-neg : Untyped
test-neg = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-neg) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))))

expected-neg : Result
expected-neg = success (UCon (tagCon bytestring (mkByteString "8bd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-neg`; postulated builtin `bls12-381-G1-uncompress`.
pending-neg : Set
pending-neg = Pending (evalRaw test-neg ≡ expected-neg)
```

## neg-zero

```
-- builtin/semantics/bls12_381_G1_neg/neg-zero
-- The negative of the zero point is the zero point.
test-neg-zero : Untyped
test-neg-zero = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UBuiltin bls12-381-G1-neg) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))))

expected-neg-zero : Result
expected-neg-zero = success (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-neg`; postulated builtin `bls12-381-G1-uncompress`.
pending-neg-zero : Set
pending-neg-zero = Pending (evalRaw test-neg-zero ≡ expected-neg-zero)
```
