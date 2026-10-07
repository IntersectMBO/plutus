---
title: Conformance.Builtin.Semantics.InsertCoin
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/insertCoin`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.InsertCoin where

open import Conformance.Eval
```

## key-too-long-1

```
-- builtin/semantics/insertCoin/key-too-long-1
-- A key larger than 32-bit, which is not allowed
test-key-too-long-1 : Untyped
test-key-too-long-1 = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon value (valueFromList ([])))))

expected-key-too-long-1 : Result
expected-key-too-long-1 = failure

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-key-too-long-1 : Set
pending-key-too-long-1 = Pending (evalRaw test-key-too-long-1 ≡ expected-key-too-long-1)
```

## key-too-long-2

```
-- builtin/semantics/insertCoin/key-too-long-2
-- A key larger than 32-bit, which is not allowed
test-key-too-long-2 : Untyped
test-key-too-long-2 = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170")))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon value (valueFromList ([])))))

expected-key-too-long-2 : Result
expected-key-too-long-2 = failure

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-key-too-long-2 : Set
pending-key-too-long-2 = Pending (evalRaw test-key-too-long-2 ≡ expected-key-too-long-2)
```

## long-key-zero-1

```
-- builtin/semantics/insertCoin/long-key-zero-1
-- A key larger than 32-bit, which is only allowed when inserting 0 value
test-long-key-zero-1 : Untyped
test-long-key-zero-1 = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-long-key-zero-1 : Result
expected-long-key-zero-1 = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ []))))

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-long-key-zero-1 : Set
pending-long-key-zero-1 = Pending (evalRaw test-long-key-zero-1 ≡ expected-long-key-zero-1)
```

## long-key-zero-2

```
-- builtin/semantics/insertCoin/long-key-zero-2
-- A key larger than 32-bit, which is only allowed when inserting 0 value
test-long-key-zero-2 : Untyped
test-long-key-zero-2 = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170\170")))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-long-key-zero-2 : Result
expected-long-key-zero-2 = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ []))))

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-long-key-zero-2 : Set
pending-long-key-zero-2 = Pending (evalRaw test-long-key-zero-2 ≡ expected-long-key-zero-2)
```

## multi-ccy-empty

```
-- builtin/semantics/insertCoin/multi-ccy-empty
test-multi-ccy-empty : Untyped
test-multi-ccy-empty = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-multi-ccy-empty : Result
expected-multi-ccy-empty = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "\NUL") , (((mkByteString "\NUL") , (ℤ.pos 1)) ∷ [])) ∷ []))))

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-multi-ccy-empty : Set
pending-multi-ccy-empty = Pending (evalRaw test-multi-ccy-empty ≡ expected-multi-ccy-empty)
```

## multi-ccy-nonempty

```
-- builtin/semantics/insertCoin/multi-ccy-nonempty
test-multi-ccy-nonempty : Untyped
test-multi-ccy-nonempty = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "\170")))) (UCon (tagCon bytestring (mkByteString "\170")))) (UCon (tagCon integer (ℤ.pos 5)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-multi-ccy-nonempty : Result
expected-multi-ccy-nonempty = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 5)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ []))))

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-multi-ccy-nonempty : Set
pending-multi-ccy-nonempty = Pending (evalRaw test-multi-ccy-nonempty ≡ expected-multi-ccy-nonempty)
```

## multi-token

```
-- builtin/semantics/insertCoin/multi-token
test-multi-token : Untyped
test-multi-token = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "\170")))) (UCon (tagCon bytestring (mkByteString "\187")))) (UCon (tagCon integer (ℤ.pos 10)))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 5)) ∷ ((mkByteString "\187") , (ℤ.pos 15)) ∷ ((mkByteString "\204") , (ℤ.pos 20)) ∷ [])) ∷ [])))))

expected-multi-token : Result
expected-multi-token = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 5)) ∷ ((mkByteString "\187") , (ℤ.pos 10)) ∷ ((mkByteString "\204") , (ℤ.pos 20)) ∷ [])) ∷ []))))

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-multi-token : Set
pending-multi-token = Pending (evalRaw test-multi-token ≡ expected-multi-token)
```

## negative-empty

```
-- builtin/semantics/insertCoin/negative-empty
test-negative-empty : Untyped
test-negative-empty = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.negsuc 0)))) (UCon (tagCon value (valueFromList ([])))))

expected-negative-empty : Result
expected-negative-empty = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.negsuc 0)) ∷ [])) ∷ []))))

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-negative-empty : Set
pending-negative-empty = Pending (evalRaw test-negative-empty ≡ expected-negative-empty)
```

## no-overflow

```
-- builtin/semantics/insertCoin/no-overflow
-- Inserts 2^17 - 1, which is the maximum allowed value for a token
test-no-overflow : Untyped
test-no-overflow = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.pos 170141183460469231731687303715884105727)))) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-no-overflow : Result
expected-no-overflow = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-no-overflow : Set
pending-no-overflow = Pending (evalRaw test-no-overflow ≡ expected-no-overflow)
```

## no-underflow

```
-- builtin/semantics/insertCoin/no-underflow
-- Inserts -2^127, which is the minimum allowed value of a token
test-no-underflow : Untyped
test-no-underflow = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.negsuc 170141183460469231731687303715884105727)))) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-no-underflow : Result
expected-no-underflow = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ []))))

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-no-underflow : Set
pending-no-underflow = Pending (evalRaw test-no-underflow ≡ expected-no-underflow)
```

## overflow

```
-- builtin/semantics/insertCoin/overflow
-- Inserts 2^127, which exceeds the maximum value of a token
test-overflow : Untyped
test-overflow = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.pos 170141183460469231731687303715884105728)))) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-overflow : Result
expected-overflow = failure

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-overflow : Set
pending-overflow = Pending (evalRaw test-overflow ≡ expected-overflow)
```

## positive-empty

```
-- builtin/semantics/insertCoin/positive-empty
test-positive-empty : Untyped
test-positive-empty = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon value (valueFromList ([])))))

expected-positive-empty : Result
expected-positive-empty = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ []))))

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-positive-empty : Set
pending-positive-empty = Pending (evalRaw test-positive-empty ≡ expected-positive-empty)
```

## positive-nonempty

```
-- builtin/semantics/insertCoin/positive-nonempty
test-positive-nonempty : Untyped
test-positive-nonempty = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-positive-nonempty : Result
expected-positive-nonempty = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ []))))

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-positive-nonempty : Set
pending-positive-nonempty = Pending (evalRaw test-positive-nonempty ≡ expected-positive-nonempty)
```

## underflow

```
-- builtin/semantics/insertCoin/underflow
-- Inserts -2^127 - 1, which exceeds the minimum allowed value of a token
test-underflow : Untyped
test-underflow = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.negsuc 170141183460469231731687303715884105728)))) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-underflow : Result
expected-underflow = failure

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-underflow : Set
pending-underflow = Pending (evalRaw test-underflow ≡ expected-underflow)
```

## zero-positive

```
-- builtin/semantics/insertCoin/zero-positive
test-zero-positive : Untyped
test-zero-positive = (UApp (UApp (UApp (UApp (UBuiltin insertCoin) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-zero-positive : Result
expected-zero-positive = success (UCon (tagCon value (valueFromList ([]))))

-- Pending: bytestring constant; value constant; postulated builtin `insertCoin`.
pending-zero-positive : Set
pending-zero-positive = Pending (evalRaw test-zero-positive ≡ expected-zero-positive)
```
