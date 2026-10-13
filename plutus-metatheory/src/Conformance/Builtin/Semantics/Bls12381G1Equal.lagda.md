---
title: Conformance.Builtin.Semantics.Bls12381G1Equal
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G1_equal`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G1Equal where

open import Conformance.Eval
```

## equal-false

```
-- builtin/semantics/bls12_381_G1_equal/equal-false
test-equal-false : Untyped
test-equal-false = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))

expected-equal-false : Result
expected-equal-false = success (UCon (tagCon bool false))

-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-uncompress`.
pending-equal-false : Set
pending-equal-false = Pending (evalRaw test-equal-false ≡ expected-equal-false)
```

## equal-true

```
-- builtin/semantics/bls12_381_G1_equal/equal-true
test-equal-true : Untyped
test-equal-true = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))))

expected-equal-true : Result
expected-equal-true = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-uncompress`.
pending-equal-true : Set
pending-equal-true = Pending (evalRaw test-equal-true ≡ expected-equal-true)
```
