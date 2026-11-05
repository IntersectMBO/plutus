---
title: Conformance.Builtin.Semantics.ScaleValue
layout: page
---

<!-- GENERATED FILE: do not edit.
<<<<<<< HEAD
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
=======
     Regenerate with `generate-agda-typecheck-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-typecheck-conformance` from the
>>>>>>> origin/master
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
<<<<<<< HEAD
test-by-neg = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.negsuc 1)))) (UCon (tagCon value (valueFromList (((mkByteString "aa") , (((mkByteString "aa") , (ℤ.pos 5)) ∷ ((mkByteString "bb") , (ℤ.negsuc 14)) ∷ ((mkByteString "cc") , (ℤ.pos 20)) ∷ [])) ∷ [])))))

expected-by-neg : Result
expected-by-neg = success (UCon (tagCon value (valueFromList (((mkByteString "aa") , (((mkByteString "aa") , (ℤ.negsuc 9)) ∷ ((mkByteString "bb") , (ℤ.pos 30)) ∷ ((mkByteString "cc") , (ℤ.negsuc 39)) ∷ [])) ∷ []))))
=======
test-by-neg = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.negsuc 1)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 5)) ∷ ((mkByteString "\187") , (ℤ.negsuc 14)) ∷ ((mkByteString "\204") , (ℤ.pos 20)) ∷ [])) ∷ [])))))

expected-by-neg : Result
expected-by-neg = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 9)) ∷ ((mkByteString "\187") , (ℤ.pos 30)) ∷ ((mkByteString "\204") , (ℤ.negsuc 39)) ∷ [])) ∷ []))))
>>>>>>> origin/master

-- Pending: value constant; postulated builtin `scaleValue`.
pending-by-neg : Set
pending-by-neg = Pending (evalRaw test-by-neg ≡ expected-by-neg)
```

## by-pos

```
-- builtin/semantics/scaleValue/by-pos
test-by-pos : Untyped
<<<<<<< HEAD
test-by-pos = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "aa") , (((mkByteString "aa") , (ℤ.pos 5)) ∷ ((mkByteString "bb") , (ℤ.negsuc 14)) ∷ ((mkByteString "cc") , (ℤ.pos 20)) ∷ [])) ∷ [])))))

expected-by-pos : Result
expected-by-pos = success (UCon (tagCon value (valueFromList (((mkByteString "aa") , (((mkByteString "aa") , (ℤ.pos 10)) ∷ ((mkByteString "bb") , (ℤ.negsuc 29)) ∷ ((mkByteString "cc") , (ℤ.pos 40)) ∷ [])) ∷ []))))
=======
test-by-pos = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 5)) ∷ ((mkByteString "\187") , (ℤ.negsuc 14)) ∷ ((mkByteString "\204") , (ℤ.pos 20)) ∷ [])) ∷ [])))))

expected-by-pos : Result
expected-by-pos = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 10)) ∷ ((mkByteString "\187") , (ℤ.negsuc 29)) ∷ ((mkByteString "\204") , (ℤ.pos 40)) ∷ [])) ∷ []))))
>>>>>>> origin/master

-- Pending: value constant; postulated builtin `scaleValue`.
pending-by-pos : Set
pending-by-pos = Pending (evalRaw test-by-pos ≡ expected-by-pos)
```

## by-zero

```
-- builtin/semantics/scaleValue/by-zero
test-by-zero : Untyped
<<<<<<< HEAD
test-by-zero = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon value (valueFromList (((mkByteString "aa") , (((mkByteString "aa") , (ℤ.pos 5)) ∷ ((mkByteString "bb") , (ℤ.negsuc 14)) ∷ ((mkByteString "cc") , (ℤ.pos 20)) ∷ [])) ∷ [])))))
=======
test-by-zero = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 5)) ∷ ((mkByteString "\187") , (ℤ.negsuc 14)) ∷ ((mkByteString "\204") , (ℤ.pos 20)) ∷ [])) ∷ [])))))
>>>>>>> origin/master

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
<<<<<<< HEAD
test-no-overflow = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "aa") , (((mkByteString "aa") , (ℤ.pos 85070591730234615865843651857942052863)) ∷ [])) ∷ [])))))

expected-no-overflow : Result
expected-no-overflow = success (UCon (tagCon value (valueFromList (((mkByteString "aa") , (((mkByteString "aa") , (ℤ.pos 170141183460469231731687303715884105726)) ∷ [])) ∷ []))))
=======
test-no-overflow = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 85070591730234615865843651857942052863)) ∷ [])) ∷ [])))))

expected-no-overflow : Result
expected-no-overflow = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 170141183460469231731687303715884105726)) ∷ [])) ∷ []))))
>>>>>>> origin/master

-- Pending: value constant; postulated builtin `scaleValue`.
pending-no-overflow : Set
pending-no-overflow = Pending (evalRaw test-no-overflow ≡ expected-no-overflow)
```

## no-underflow

```
-- builtin/semantics/scaleValue/no-underflow
-- This computes -(2^127), which is the minimum allowed value
test-no-underflow : Untyped
<<<<<<< HEAD
test-no-underflow = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "aa") , (((mkByteString "aa") , (ℤ.negsuc 85070591730234615865843651857942052863)) ∷ [])) ∷ [])))))

expected-no-underflow : Result
expected-no-underflow = success (UCon (tagCon value (valueFromList (((mkByteString "aa") , (((mkByteString "aa") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))
=======
test-no-underflow = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 85070591730234615865843651857942052863)) ∷ [])) ∷ [])))))

expected-no-underflow : Result
expected-no-underflow = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))
>>>>>>> origin/master

-- Pending: value constant; postulated builtin `scaleValue`.
pending-no-underflow : Set
pending-no-underflow = Pending (evalRaw test-no-underflow ≡ expected-no-underflow)
```

## overflow

```
-- builtin/semantics/scaleValue/overflow
-- Performs 2 * 2^126 = 2^127 which exceeds the maximum allowed value (2^127 - 1)
test-overflow : Untyped
<<<<<<< HEAD
test-overflow = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "aa") , (((mkByteString "aa") , (ℤ.pos 85070591730234615865843651857942052864)) ∷ [])) ∷ [])))))
=======
test-overflow = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 85070591730234615865843651857942052864)) ∷ [])) ∷ [])))))
>>>>>>> origin/master

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
<<<<<<< HEAD
test-underflow = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "aa") , (((mkByteString "aa") , (ℤ.negsuc 85070591730234615865843651857942052864)) ∷ [])) ∷ [])))))
=======
test-underflow = (UApp (UApp (UBuiltin scaleValue) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 85070591730234615865843651857942052864)) ∷ [])) ∷ [])))))
>>>>>>> origin/master

expected-underflow : Result
expected-underflow = failure

-- Pending: value constant; postulated builtin `scaleValue`.
pending-underflow : Set
pending-underflow = Pending (evalRaw test-underflow ≡ expected-underflow)
```
