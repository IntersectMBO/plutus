---
title: Conformance.Builtin.Semantics.IndexArray
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/indexArray`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.IndexArray where

open import Conformance.Eval
```

## indexArray-01

```
-- builtin/semantics/indexArray/indexArray-01
-- Taking an array element by index
test-indexArray-01 : Untyped
test-indexArray-01 = (UApp (UApp (UForce (UBuiltin indexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 1) ∷ (ℤ.pos 2) ∷ (ℤ.pos 3) ∷ (ℤ.pos 4) ∷ (ℤ.pos 5) ∷ [])))))) (UCon (tagCon integer (ℤ.pos 1))))

expected-indexArray-01 : Result
expected-indexArray-01 = success (UCon (tagCon integer (ℤ.pos 2)))

-- Pending: array constant; postulated builtin `indexArray`.
pending-indexArray-01 : Set
pending-indexArray-01 = Pending (evalRaw test-indexArray-01 ≡ expected-indexArray-01)
```

## indexArray-02

```
-- builtin/semantics/indexArray/indexArray-02
-- Taking an array element by index which is out of bounds
test-indexArray-02 : Untyped
test-indexArray-02 = (UApp (UApp (UForce (UBuiltin indexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 1) ∷ (ℤ.pos 2) ∷ (ℤ.pos 3) ∷ (ℤ.pos 4) ∷ (ℤ.pos 5) ∷ [])))))) (UCon (tagCon integer (ℤ.pos 5))))

expected-indexArray-02 : Result
expected-indexArray-02 = failure

-- Pending: array constant; postulated builtin `indexArray`.
pending-indexArray-02 : Set
pending-indexArray-02 = Pending (evalRaw test-indexArray-02 ≡ expected-indexArray-02)
```

## indexArray-03

```
-- builtin/semantics/indexArray/indexArray-03
-- Taking an array element by a negative index
test-indexArray-03 : Untyped
test-indexArray-03 = (UApp (UApp (UForce (UBuiltin indexArray)) (UCon (tagCon (array integer) (mkArray (((ℤ.pos 1) ∷ (ℤ.pos 2) ∷ (ℤ.pos 3) ∷ (ℤ.pos 4) ∷ (ℤ.pos 5) ∷ [])))))) (UCon (tagCon integer (ℤ.negsuc 0))))

expected-indexArray-03 : Result
expected-indexArray-03 = failure

-- Pending: array constant; postulated builtin `indexArray`.
pending-indexArray-03 : Set
pending-indexArray-03 = Pending (evalRaw test-indexArray-03 ≡ expected-indexArray-03)
```
