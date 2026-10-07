---
title: Conformance.Builtin.Semantics.ValueContains
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/valueContains`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ValueContains where

open import Conformance.Eval
```

## ccy-missing

```
-- builtin/semantics/valueContains/ccy-missing
test-ccy-missing : Untyped
test-ccy-missing = (UApp (UApp (UBuiltin valueContains) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 10)) ∷ ((mkByteString "\187") , (ℤ.pos 2800)) ∷ [])) ∷ ((mkByteString "\255\255") , (((mkByteString "\136\136") , (ℤ.pos 100)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\DC24") , (((mkByteString "\171\205") , (ℤ.pos 20)) ∷ [])) ∷ ((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 10)) ∷ [])) ∷ [])))))

expected-ccy-missing : Result
expected-ccy-missing = success (UCon (tagCon bool false))

-- Pending: value constant; postulated builtin `valueContains`.
pending-ccy-missing : Set
pending-ccy-missing = Pending (evalRaw test-ccy-missing ≡ expected-ccy-missing)
```

## multi-insufficient

```
-- builtin/semantics/valueContains/multi-insufficient
test-multi-insufficient : Untyped
test-multi-insufficient = (UApp (UApp (UBuiltin valueContains) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 10)) ∷ ((mkByteString "\187") , (ℤ.pos 2800)) ∷ [])) ∷ ((mkByteString "\255\255") , (((mkByteString "\136\136") , (ℤ.pos 100)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 10)) ∷ [])) ∷ ((mkByteString "\255\255") , (((mkByteString "\136\136") , (ℤ.pos 101)) ∷ [])) ∷ [])))))

expected-multi-insufficient : Result
expected-multi-insufficient = success (UCon (tagCon bool false))

-- Pending: value constant; postulated builtin `valueContains`.
pending-multi-insufficient : Set
pending-multi-insufficient = Pending (evalRaw test-multi-insufficient ≡ expected-multi-insufficient)
```

## multi-sufficient

```
-- builtin/semantics/valueContains/multi-sufficient
test-multi-sufficient : Untyped
test-multi-sufficient = (UApp (UApp (UBuiltin valueContains) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 10)) ∷ ((mkByteString "\187") , (ℤ.pos 2800)) ∷ [])) ∷ ((mkByteString "\255\255") , (((mkByteString "\136\136") , (ℤ.pos 100)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 10)) ∷ [])) ∷ ((mkByteString "\255\255") , (((mkByteString "\136\136") , (ℤ.pos 20)) ∷ [])) ∷ [])))))

expected-multi-sufficient : Result
expected-multi-sufficient = success (UCon (tagCon bool true))

-- Pending: value constant; postulated builtin `valueContains`.
pending-multi-sufficient : Set
pending-multi-sufficient = Pending (evalRaw test-multi-sufficient ≡ expected-multi-sufficient)
```

## neg-empty

```
-- builtin/semantics/valueContains/neg-empty
test-neg-empty : Untyped
test-neg-empty = (UApp (UApp (UBuiltin valueContains) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 99)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\170") , (ℤ.negsuc 0)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList ([])))))

expected-neg-empty : Result
expected-neg-empty = failure

-- Pending: value constant; postulated builtin `valueContains`.
pending-neg-empty : Set
pending-neg-empty = Pending (evalRaw test-neg-empty ≡ expected-neg-empty)
```

## neg-neg-eq

```
-- builtin/semantics/valueContains/neg-neg-eq
test-neg-neg-eq : Untyped
test-neg-neg-eq = (UApp (UApp (UBuiltin valueContains) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 9)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 9)) ∷ [])) ∷ [])))))

expected-neg-neg-eq : Result
expected-neg-neg-eq = failure

-- Pending: value constant; postulated builtin `valueContains`.
pending-neg-neg-eq : Set
pending-neg-neg-eq = Pending (evalRaw test-neg-neg-eq ≡ expected-neg-neg-eq)
```

## neg-neg-gt

```
-- builtin/semantics/valueContains/neg-neg-gt
test-neg-neg-gt : Untyped
test-neg-neg-gt = (UApp (UApp (UBuiltin valueContains) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 9)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 8)) ∷ [])) ∷ [])))))

expected-neg-neg-gt : Result
expected-neg-neg-gt = failure

-- Pending: value constant; postulated builtin `valueContains`.
pending-neg-neg-gt : Set
pending-neg-neg-gt = Pending (evalRaw test-neg-neg-gt ≡ expected-neg-neg-gt)
```

## neg-neg-lt

```
-- builtin/semantics/valueContains/neg-neg-lt
test-neg-neg-lt : Untyped
test-neg-neg-lt = (UApp (UApp (UBuiltin valueContains) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 9)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 10)) ∷ [])) ∷ [])))))

expected-neg-neg-lt : Result
expected-neg-neg-lt = failure

-- Pending: value constant; postulated builtin `valueContains`.
pending-neg-neg-lt : Set
pending-neg-neg-lt = Pending (evalRaw test-neg-neg-lt ≡ expected-neg-neg-lt)
```

## neg-pos

```
-- builtin/semantics/valueContains/neg-pos
test-neg-pos : Untyped
test-neg-pos = (UApp (UApp (UBuiltin valueContains) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 9)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 100)) ∷ [])) ∷ [])))))

expected-neg-pos : Result
expected-neg-pos = failure

-- Pending: value constant; postulated builtin `valueContains`.
pending-neg-pos : Set
pending-neg-pos = Pending (evalRaw test-neg-pos ≡ expected-neg-pos)
```

## pos-empty

```
-- builtin/semantics/valueContains/pos-empty
test-pos-empty : Untyped
test-pos-empty = (UApp (UApp (UBuiltin valueContains) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 100)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList ([])))))

expected-pos-empty : Result
expected-pos-empty = success (UCon (tagCon bool true))

-- Pending: value constant; postulated builtin `valueContains`.
pending-pos-empty : Set
pending-pos-empty = Pending (evalRaw test-pos-empty ≡ expected-pos-empty)
```

## pos-neg

```
-- builtin/semantics/valueContains/pos-neg
test-pos-neg : Untyped
test-pos-neg = (UApp (UApp (UBuiltin valueContains) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 100)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.negsuc 9)) ∷ [])) ∷ [])))))

expected-pos-neg : Result
expected-pos-neg = failure

-- Pending: value constant; postulated builtin `valueContains`.
pending-pos-neg : Set
pending-pos-neg = Pending (evalRaw test-pos-neg ≡ expected-pos-neg)
```

## reflexive

```
-- builtin/semantics/valueContains/reflexive
test-reflexive : Untyped
test-reflexive = (UApp (UApp (UBuiltin valueContains) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 100)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 100)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-reflexive : Result
expected-reflexive = success (UCon (tagCon bool true))

-- Pending: value constant; postulated builtin `valueContains`.
pending-reflexive : Set
pending-reflexive = Pending (evalRaw test-reflexive ≡ expected-reflexive)
```

## token-missing

```
-- builtin/semantics/valueContains/token-missing
test-token-missing : Untyped
test-token-missing = (UApp (UApp (UBuiltin valueContains) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\187") , (ℤ.pos 100)) ∷ ((mkByteString "\204") , (ℤ.pos 2800)) ∷ [])) ∷ []))))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\221") , (ℤ.pos 5)) ∷ [])) ∷ [])))))

expected-token-missing : Result
expected-token-missing = success (UCon (tagCon bool false))

-- Pending: value constant; postulated builtin `valueContains`.
pending-token-missing : Set
pending-token-missing = Pending (evalRaw test-token-missing ≡ expected-token-missing)
```
