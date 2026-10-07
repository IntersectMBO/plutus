---
title: Conformance.Builtin.Semantics.UnionValue
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/unionValue`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.UnionValue where

open import Conformance.Eval
```

## cancel-01

```
-- builtin/semantics/unionValue/cancel-01
test-cancel-01 : Untyped
test-cancel-01 = (UApp (UApp (UBuiltin unionValue) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 100000)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.negsuc 99999)) ∷ [])) ∷ [])))))

expected-cancel-01 : Result
expected-cancel-01 = success (UCon (tagCon value (valueFromList ([]))))

-- Pending: value constant; postulated builtin `unionValue`.
pending-cancel-01 : Set
pending-cancel-01 = Pending (evalRaw test-cancel-01 ≡ expected-cancel-01)
```

## cancel-02

```
-- builtin/semantics/unionValue/cancel-02
test-cancel-02 : Untyped
test-cancel-02 = (UApp (UApp (UBuiltin unionValue) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.negsuc 99999)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 100000)) ∷ [])) ∷ [])))))

expected-cancel-02 : Result
expected-cancel-02 = success (UCon (tagCon value (valueFromList ([]))))

-- Pending: value constant; postulated builtin `unionValue`.
pending-cancel-02 : Set
pending-cancel-02 = Pending (evalRaw test-cancel-02 ≡ expected-cancel-02)
```

## combine

```
-- builtin/semantics/unionValue/combine
test-combine : Untyped
test-combine = (UApp (UApp (UBuiltin unionValue) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 100000)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 100000)) ∷ [])) ∷ [])))))

expected-combine : Result
expected-combine = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 200000)) ∷ [])) ∷ []))))

-- Pending: value constant; postulated builtin `unionValue`.
pending-combine : Set
pending-combine = Pending (evalRaw test-combine ≡ expected-combine)
```

## no-overflow

```
-- builtin/semantics/unionValue/no-overflow
-- This adds up to 2^127 - 1, the maximum allowed value for a single token
test-no-overflow : Untyped
test-no-overflow = (UApp (UApp (UBuiltin unionValue) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 170141183460469231731687303715884105726)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-no-overflow : Result
expected-no-overflow = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))

-- Pending: value constant; postulated builtin `unionValue`.
pending-no-overflow : Set
pending-no-overflow = Pending (evalRaw test-no-overflow ≡ expected-no-overflow)
```

## no-underflow

```
-- builtin/semantics/unionValue/no-underflow
-- This adds up to -2^-127, which is the minimum allowed value for a single
-- token
test-no-underflow : Untyped
test-no-underflow = (UApp (UApp (UBuiltin unionValue) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 170141183460469231731687303715884105726)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 0)) ∷ [])) ∷ [])))))

expected-no-underflow : Result
expected-no-underflow = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))

-- Pending: value constant; postulated builtin `unionValue`.
pending-no-underflow : Set
pending-no-underflow = Pending (evalRaw test-no-underflow ≡ expected-no-underflow)
```

## overflow

```
-- builtin/semantics/unionValue/overflow
-- This would add up to 2^127, which is over the allowed maximum value of a
-- token
test-overflow : Untyped
test-overflow = (UApp (UApp (UBuiltin unionValue) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-overflow : Result
expected-overflow = failure

-- Pending: value constant; postulated builtin `unionValue`.
pending-overflow : Set
pending-overflow = Pending (evalRaw test-overflow ≡ expected-overflow)
```

## underflow

```
-- builtin/semantics/unionValue/underflow
-- This would add up to (-2^-127 - 1), which is less than the allowed minimum value of a
-- token
test-underflow : Untyped
test-underflow = (UApp (UApp (UBuiltin unionValue) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 0)) ∷ [])) ∷ [])))))

expected-underflow : Result
expected-underflow = failure

-- Pending: value constant; postulated builtin `unionValue`.
pending-underflow : Set
pending-underflow = Pending (evalRaw test-underflow ≡ expected-underflow)
```

## unitl

```
-- builtin/semantics/unionValue/unitl
test-unitl : Untyped
test-unitl = (UApp (UApp (UBuiltin unionValue) (UCon (tagCon value (valueFromList ([]))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 100000)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\170") , (ℤ.pos 125)) ∷ [])) ∷ [])))))

expected-unitl : Result
expected-unitl = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 100000)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\170") , (ℤ.pos 125)) ∷ [])) ∷ []))))

-- Pending: value constant; postulated builtin `unionValue`.
pending-unitl : Set
pending-unitl = Pending (evalRaw test-unitl ≡ expected-unitl)
```

## unitr

```
-- builtin/semantics/unionValue/unitr
test-unitr : Untyped
test-unitr = (UApp (UApp (UBuiltin unionValue) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 100000)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\170") , (ℤ.pos 125)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList ([])))))

expected-unitr : Result
expected-unitr = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 100000)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\170") , (ℤ.pos 125)) ∷ [])) ∷ []))))

-- Pending: value constant; postulated builtin `unionValue`.
pending-unitr : Set
pending-unitr = Pending (evalRaw test-unitr ≡ expected-unitr)
```
