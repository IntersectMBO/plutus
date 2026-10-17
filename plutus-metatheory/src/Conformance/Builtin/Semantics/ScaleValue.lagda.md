---
title: Conformance.Builtin.Semantics.ScaleValue
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/scaleValue`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ScaleValue where

open import Conformance.Eval
```

## by-neg

```
-- builtin/semantics/scaleValue/by-neg
test-by-neg : Untyped
test-by-neg = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.negsuc 1)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 5)) ∷ ((mkByteString "\187") , (ℤ.negsuc 14)) ∷ ((mkByteString "\204") , (ℤ.pos 20)) ∷ [])) ∷ [])))))

expected-by-neg : Result
expected-by-neg = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 9)) ∷ ((mkByteString "\187") , (ℤ.pos 30)) ∷ ((mkByteString "\204") , (ℤ.negsuc 39)) ∷ [])) ∷ []))))

-- Pending: value constant; postulated builtin `scaleValue`.
pending-by-neg : Set
pending-by-neg = Pending (evalRaw test-by-neg ≡ expected-by-neg)
```

## by-pos

```
-- builtin/semantics/scaleValue/by-pos
test-by-pos : Untyped
test-by-pos = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 5)) ∷ ((mkByteString "\187") , (ℤ.negsuc 14)) ∷ ((mkByteString "\204") , (ℤ.pos 20)) ∷ [])) ∷ [])))))

expected-by-pos : Result
expected-by-pos = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 10)) ∷ ((mkByteString "\187") , (ℤ.negsuc 29)) ∷ ((mkByteString "\204") , (ℤ.pos 40)) ∷ [])) ∷ []))))

-- Pending: value constant; postulated builtin `scaleValue`.
pending-by-pos : Set
pending-by-pos = Pending (evalRaw test-by-pos ≡ expected-by-pos)
```

## by-zero

```
-- builtin/semantics/scaleValue/by-zero
test-by-zero : Untyped
test-by-zero = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 5)) ∷ ((mkByteString "\187") , (ℤ.negsuc 14)) ∷ ((mkByteString "\204") , (ℤ.pos 20)) ∷ [])) ∷ [])))))

expected-by-zero : Result
expected-by-zero = success (UCon (tagCon value (valueFromList ([]))))

-- Pending: value constant; postulated builtin `scaleValue`.
pending-by-zero : Set
pending-by-zero = Pending (evalRaw test-by-zero ≡ expected-by-zero)
```

## no-overflow

```
-- builtin/semantics/scaleValue/no-overflow
-- Computes (2^127) - 2, which stays under the maximum allowed value (2^127 - 1)
test-no-overflow : Untyped
test-no-overflow = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 85070591730234615865843651857942052863)) ∷ [])) ∷ [])))))

expected-no-overflow : Result
expected-no-overflow = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 170141183460469231731687303715884105726)) ∷ [])) ∷ []))))

-- Pending: value constant; postulated builtin `scaleValue`.
pending-no-overflow : Set
pending-no-overflow = Pending (evalRaw test-no-overflow ≡ expected-no-overflow)
```

## no-underflow

```
-- builtin/semantics/scaleValue/no-underflow
-- This computes -(2^127), which is the minimum allowed value
test-no-underflow : Untyped
test-no-underflow = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 85070591730234615865843651857942052863)) ∷ [])) ∷ [])))))

expected-no-underflow : Result
expected-no-underflow = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))

-- Pending: value constant; postulated builtin `scaleValue`.
pending-no-underflow : Set
pending-no-underflow = Pending (evalRaw test-no-underflow ≡ expected-no-underflow)
```

## overflow

```
-- builtin/semantics/scaleValue/overflow
-- Performs 2 * 2^126 = 2^127 which exceeds the maximum allowed value (2^127 - 1)
test-overflow : Untyped
test-overflow = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 85070591730234615865843651857942052864)) ∷ [])) ∷ [])))))

expected-overflow : Result
expected-overflow = failure

-- Pending: value constant; postulated builtin `scaleValue`.
pending-overflow : Set
pending-overflow = Pending (evalRaw test-overflow ≡ expected-overflow)
```

## underflow

```
-- builtin/semantics/scaleValue/underflow
-- Computes -(2^127) - 2, which exceeds the minimum allowed vallue of -(2^127)
test-underflow : Untyped
test-underflow = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 85070591730234615865843651857942052864)) ∷ [])) ∷ [])))))

expected-underflow : Result
expected-underflow = failure

-- Pending: value constant; postulated builtin `scaleValue`.
pending-underflow : Set
pending-underflow = Pending (evalRaw test-underflow ≡ expected-underflow)
```
