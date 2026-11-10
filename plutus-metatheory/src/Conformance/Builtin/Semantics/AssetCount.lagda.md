---
title: Conformance.Builtin.Semantics.AssetCount
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-typecheck-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-typecheck-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/assetCount`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.AssetCount where

open import Conformance.Eval
```

## assetCount-01

```
-- builtin/semantics/assetCount/assetCount-01
-- Empty Value
test-assetCount-01 : Untyped
test-assetCount-01 = (UApp (UBuiltin assetCount) (UCon (tagCon value (valueFromList ([])))))

expected-assetCount-01 : Result
expected-assetCount-01 = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: value constant; postulated builtin `assetCount`.
pending-assetCount-01 : Set
pending-assetCount-01 = Pending (evalRaw test-assetCount-01 ≡ expected-assetCount-01)
```

## assetCount-02

```
-- builtin/semantics/assetCount/assetCount-02
-- Lovelace and native assets
test-assetCount-02 : Untyped
test-assetCount-02 = (UApp (UBuiltin assetCount) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1000000)) ∷ [])) ∷ ((mkByteString "\170") , (((mkByteString "\SOH") , (ℤ.pos 42)) ∷ ((mkByteString "\STX") , (ℤ.pos 7)) ∷ [])) ∷ [])))))

expected-assetCount-02 : Result
expected-assetCount-02 = success (UCon (tagCon integer (ℤ.pos 3)))

-- Pending: value constant; postulated builtin `assetCount`.
pending-assetCount-02 : Set
pending-assetCount-02 = Pending (evalRaw test-assetCount-02 ≡ expected-assetCount-02)
```

## assetCount-03

```
-- builtin/semantics/assetCount/assetCount-03
-- Lovelace only
test-assetCount-03 : Untyped
test-assetCount-03 = (UApp (UBuiltin assetCount) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1000000)) ∷ [])) ∷ [])))))

expected-assetCount-03 : Result
expected-assetCount-03 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: value constant; postulated builtin `assetCount`.
pending-assetCount-03 : Set
pending-assetCount-03 = Pending (evalRaw test-assetCount-03 ≡ expected-assetCount-03)
```

## assetCount-04

```
-- builtin/semantics/assetCount/assetCount-04
-- Several token names under one policy
test-assetCount-04 : Untyped
test-assetCount-04 = (UApp (UBuiltin assetCount) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "") , (ℤ.pos 1)) ∷ ((mkByteString "\NUL") , (ℤ.pos 2)) ∷ ((mkByteString "\SOH") , (ℤ.pos 3)) ∷ [])) ∷ [])))))

expected-assetCount-04 : Result
expected-assetCount-04 = success (UCon (tagCon integer (ℤ.pos 3)))

-- Pending: value constant; postulated builtin `assetCount`.
pending-assetCount-04 : Set
pending-assetCount-04 = Pending (evalRaw test-assetCount-04 ≡ expected-assetCount-04)
```

## assetCount-05

```
-- builtin/semantics/assetCount/assetCount-05
-- Multiple policies and signed quantities
test-assetCount-05 : Untyped
test-assetCount-05 = (UApp (UBuiltin assetCount) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1000000)) ∷ [])) ∷ ((mkByteString "\170") , (((mkByteString "\SOH") , (ℤ.pos 5)) ∷ ((mkByteString "\STX") , (ℤ.negsuc 6)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "") , (ℤ.negsuc 1)) ∷ ((mkByteString "\255") , (ℤ.pos 9)) ∷ [])) ∷ ((mkByteString "\204") , (((mkByteString "\SOH") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-assetCount-05 : Result
expected-assetCount-05 = success (UCon (tagCon integer (ℤ.pos 6)))

-- Pending: value constant; postulated builtin `assetCount`.
pending-assetCount-05 : Set
pending-assetCount-05 = Pending (evalRaw test-assetCount-05 ≡ expected-assetCount-05)
```

## assetCount-06

```
-- builtin/semantics/assetCount/assetCount-06
-- Quantity and key boundaries
test-assetCount-06 : Untyped
test-assetCount-06 = (UApp (UBuiltin assetCount) (UCon (tagCon value (valueFromList (((mkByteString "\NUL") , (((mkByteString "") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ ((mkByteString "\NUL\NUL") , (((mkByteString "\SOH") , (ℤ.pos 170141183460469231731687303715884105727)) ∷ [])) ∷ ((mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255") , (((mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255") , (ℤ.negsuc 0)) ∷ [])) ∷ [])))))

expected-assetCount-06 : Result
expected-assetCount-06 = success (UCon (tagCon integer (ℤ.pos 3)))

-- Pending: value constant; postulated builtin `assetCount`.
pending-assetCount-06 : Set
pending-assetCount-06 = Pending (evalRaw test-assetCount-06 ≡ expected-assetCount-06)
```
