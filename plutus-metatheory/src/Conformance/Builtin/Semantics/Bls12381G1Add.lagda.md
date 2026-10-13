---
title: Conformance.Builtin.Semantics.Bls12381G1Add
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/bls12_381_G1_add`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Bls12381G1Add where

open import Conformance.Eval
```

## add

```
-- builtin/semantics/bls12_381_G1_add/add
-- Adding a random pair of points in G1
test-add : Untyped
test-add = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))))

expected-add : Result
expected-add = success (UCon (tagCon bytestring (mkByteString "a4870e983a149bb1e7cc70fde907a2aa52302833bce4d62f679819022924e9caab52e3631d376d36d9692664b4cfbc22")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`.
pending-add : Set
pending-add = Pending (evalRaw test-add ≡ expected-add)
```

## add-associative

```
-- builtin/semantics/bls12_381_G1_add/add-associative
-- p+(q+r) = (p+q)+r for three random points on G1.
test-add-associative : Untyped
test-add-associative = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "b962fd0cc81048e0cf7557bf3e4b6edc5ab4bfb3dc87f83af428b6300727b139c404ab159bdf2eaea3f649903421537f"))))))) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5")))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "b962fd0cc81048e0cf7557bf3e4b6edc5ab4bfb3dc87f83af428b6300727b139c404ab159bdf2eaea3f649903421537f"))))))

expected-add-associative : Result
expected-add-associative = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`.
pending-add-associative : Set
pending-add-associative = Pending (evalRaw test-add-associative ≡ expected-add-associative)
```

## add-commutative

```
-- builtin/semantics/bls12_381_G1_add/add-commutative
-- p+q = q+p for two random points in G1.
test-add-commutative : Untyped
test-add-commutative = (UApp (UApp (UBuiltin bls12-381-G1-equal) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5")))))) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))))

expected-add-commutative : Result
expected-add-commutative = success (UCon (tagCon bool true))

-- Pending: postulated builtin `bls12-381-G1-equal`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`.
pending-add-commutative : Set
pending-add-commutative = Pending (evalRaw test-add-commutative ≡ expected-add-commutative)
```

## add-zero

```
-- builtin/semantics/bls12_381_G1_add/add-zero
-- Adding the zero element to a random point doesn't change it.
test-add-zero : Untyped
test-add-zero = (UApp (UBuiltin bls12-381-G1-compress) (UApp (UApp (UBuiltin bls12-381-G1-add) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f"))))) (UApp (UBuiltin bls12-381-G1-uncompress) (UCon (tagCon bytestring (mkByteString "c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))))

expected-add-zero : Result
expected-add-zero = success (UCon (tagCon bytestring (mkByteString "abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f")))

-- Pending: postulated builtin `bls12-381-G1-compress`; postulated builtin `bls12-381-G1-add`; postulated builtin `bls12-381-G1-uncompress`.
pending-add-zero : Set
pending-add-zero = Pending (evalRaw test-add-zero ≡ expected-add-zero)
```
