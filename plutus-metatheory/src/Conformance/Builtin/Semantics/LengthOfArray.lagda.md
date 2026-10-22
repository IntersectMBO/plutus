---
title: Conformance.Builtin.Semantics.LengthOfArray
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/lengthOfArray`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.LengthOfArray where

open import Conformance.Eval
```

## lengthOfArray-01

```
-- builtin/semantics/lengthOfArray/lengthOfArray-01
-- Measuring the length of an empty array
test-lengthOfArray-01 : Untyped
test-lengthOfArray-01 = (UApp (UForce (UBuiltin lengthOfArray)) (UCon (tagCon (array bool) (mkArray (([]))))))

expected-lengthOfArray-01 : Result
expected-lengthOfArray-01 = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: array constant; postulated builtin `lengthOfArray`.
pending-lengthOfArray-01 : Set
pending-lengthOfArray-01 = Pending (evalRaw test-lengthOfArray-01 ≡ expected-lengthOfArray-01)
```

## lengthOfArray-02

```
-- builtin/semantics/lengthOfArray/lengthOfArray-02
-- Measuring the length of a non-empty array
test-lengthOfArray-02 : Untyped
test-lengthOfArray-02 = (UApp (UForce (UBuiltin lengthOfArray)) (UCon (tagCon (array bool) (mkArray ((true ∷ false ∷ true ∷ []))))))

expected-lengthOfArray-02 : Result
expected-lengthOfArray-02 = success (UCon (tagCon integer (ℤ.pos 3)))

-- Pending: array constant; postulated builtin `lengthOfArray`.
pending-lengthOfArray-02 : Set
pending-lengthOfArray-02 = Pending (evalRaw test-lengthOfArray-02 ≡ expected-lengthOfArray-02)
```
