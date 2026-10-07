---
title: Conformance.Builtin.Semantics.EqualsData
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/equalsData`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.EqualsData where

open import Conformance.Eval
```

## equalsData-01

```
-- builtin/semantics/equalsData/equalsData-01
test-equalsData-01 : Untyped
test-equalsData-01 = (UApp (UApp (UBuiltin equalsData) (UCon (tagCon pdata (ConstrDATA (ℤ.pos 1) ((iDATA (ℤ.pos 0)) ∷ []))))) (UCon (tagCon pdata (ConstrDATA (ℤ.pos 1) ((iDATA (ℤ.pos 0)) ∷ [])))))

expected-equalsData-01 : Result
expected-equalsData-01 = success (UCon (tagCon bool true))

_ : evalRaw test-equalsData-01 ≡ expected-equalsData-01
_ = refl
```

## equalsData-02

```
-- builtin/semantics/equalsData/equalsData-02
test-equalsData-02 : Untyped
test-equalsData-02 = (UApp (UApp (UBuiltin equalsData) (UCon (tagCon pdata (ConstrDATA (ℤ.pos 1) ((iDATA (ℤ.pos 0)) ∷ []))))) (UCon (tagCon pdata (ConstrDATA (ℤ.pos 1) ((iDATA (ℤ.pos 1)) ∷ [])))))

expected-equalsData-02 : Result
expected-equalsData-02 = success (UCon (tagCon bool false))

_ : evalRaw test-equalsData-02 ≡ expected-equalsData-02
_ = refl
```

## equalsData-03

```
-- builtin/semantics/equalsData/equalsData-03
test-equalsData-03 : Untyped
test-equalsData-03 = (UApp (UApp (UBuiltin equalsData) (UCon (tagCon pdata (ConstrDATA (ℤ.pos 0) ((iDATA (ℤ.pos 0)) ∷ []))))) (UCon (tagCon pdata (ConstrDATA (ℤ.pos 1) ((iDATA (ℤ.pos 0)) ∷ [])))))

expected-equalsData-03 : Result
expected-equalsData-03 = success (UCon (tagCon bool false))

_ : evalRaw test-equalsData-03 ≡ expected-equalsData-03
_ = refl
```

## equalsData-04

```
-- builtin/semantics/equalsData/equalsData-04
test-equalsData-04 : Untyped
test-equalsData-04 = (UApp (UApp (UBuiltin equalsData) (UCon (tagCon pdata (ConstrDATA (ℤ.pos 17) ((iDATA (ℤ.pos 0)) ∷ []))))) (UCon (tagCon pdata (ConstrDATA (ℤ.pos 17) ((bDATA (mkByteString "\NUL")) ∷ [])))))

expected-equalsData-04 : Result
expected-equalsData-04 = success (UCon (tagCon bool false))

-- Pending: bytestring inside a `data` constant.
pending-equalsData-04 : Set
pending-equalsData-04 = Pending (evalRaw test-equalsData-04 ≡ expected-equalsData-04)
```
