---
title: Conformance.Builtin.Semantics.ListToArray
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/listToArray`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ListToArray where

open import Conformance.Eval
```

## listToArray-01

```
-- builtin/semantics/listToArray/listToArray-01
-- Convert an empty list to an array
test-listToArray-01 : Untyped
test-listToArray-01 = (UApp (UForce (UBuiltin listToArray)) (UCon (tagCon (list integer) ([]))))

expected-listToArray-01 : Result
expected-listToArray-01 = success (UCon (tagCon (array integer) (mkArray (([])))))

-- Pending: array constant; postulated builtin `listToArray`.
pending-listToArray-01 : Set
pending-listToArray-01 = Pending (evalRaw test-listToArray-01 ≡ expected-listToArray-01)
```

## listToArray-02

```
-- builtin/semantics/listToArray/listToArray-02
-- convert a non-empty list to an array
test-listToArray-02 : Untyped
test-listToArray-02 = (UApp (UForce (UBuiltin listToArray)) (UCon (tagCon (list integer) ((ℤ.pos 11) ∷ (ℤ.pos 22) ∷ (ℤ.pos 33) ∷ (ℤ.pos 44) ∷ (ℤ.pos 55) ∷ (ℤ.pos 66) ∷ (ℤ.pos 77) ∷ (ℤ.pos 88) ∷ (ℤ.pos 99) ∷ []))))

expected-listToArray-02 : Result
expected-listToArray-02 = success (UCon (tagCon (array integer) (mkArray (((ℤ.pos 11) ∷ (ℤ.pos 22) ∷ (ℤ.pos 33) ∷ (ℤ.pos 44) ∷ (ℤ.pos 55) ∷ (ℤ.pos 66) ∷ (ℤ.pos 77) ∷ (ℤ.pos 88) ∷ (ℤ.pos 99) ∷ [])))))

-- Pending: array constant; postulated builtin `listToArray`.
pending-listToArray-02 : Set
pending-listToArray-02 = Pending (evalRaw test-listToArray-02 ≡ expected-listToArray-02)
```
