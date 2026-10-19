---
title: Conformance.Builtin.Semantics.UnValueData
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/unValueData`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.UnValueData where

open import Conformance.Eval
```

## currency-key-too-long

```
-- builtin/semantics/unValueData/currency-key-too-long
-- Currency symbol with 33 bytes (> maxKeyLen)
test-currency-key-too-long : Untyped
test-currency-key-too-long = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")) , (MapDATA (((bDATA (mkByteString "")) , (iDATA (ℤ.pos 1))) ∷ []))) ∷ [])))))

expected-currency-key-too-long : Result
expected-currency-key-too-long = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-currency-key-too-long : Set
pending-currency-key-too-long = Pending (evalRaw test-currency-key-too-long ≡ expected-currency-key-too-long)
```

## data-duplicate-currencies

```
-- builtin/semantics/unValueData/data-duplicate-currencies
test-data-duplicate-currencies : Untyped
test-data-duplicate-currencies = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 100))) ∷ []))) ∷ ((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\204")) , (iDATA (ℤ.pos 50))) ∷ []))) ∷ [])))))

expected-data-duplicate-currencies : Result
expected-data-duplicate-currencies = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-data-duplicate-currencies : Set
pending-data-duplicate-currencies = Pending (evalRaw test-data-duplicate-currencies ≡ expected-data-duplicate-currencies)
```

## data-duplicate-currencies-cancel

```
-- builtin/semantics/unValueData/data-duplicate-currencies-cancel
test-data-duplicate-currencies-cancel : Untyped
test-data-duplicate-currencies-cancel = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\170")) , (iDATA (ℤ.pos 123))) ∷ []))) ∷ ((bDATA (mkByteString "\187")) , (MapDATA (((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 2))) ∷ []))) ∷ ((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\170")) , (iDATA (ℤ.negsuc 79))) ∷ []))) ∷ ((bDATA (mkByteString "\204")) , (MapDATA (((bDATA (mkByteString "\204")) , (iDATA (ℤ.pos 2))) ∷ []))) ∷ ((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\170")) , (iDATA (ℤ.negsuc 42))) ∷ []))) ∷ [])))))

expected-data-duplicate-currencies-cancel : Result
expected-data-duplicate-currencies-cancel = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-data-duplicate-currencies-cancel : Set
pending-data-duplicate-currencies-cancel = Pending (evalRaw test-data-duplicate-currencies-cancel ≡ expected-data-duplicate-currencies-cancel)
```

## data-duplicate-currencies-merge

```
-- builtin/semantics/unValueData/data-duplicate-currencies-merge
test-data-duplicate-currencies-merge : Untyped
test-data-duplicate-currencies-merge = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\170")) , (iDATA (ℤ.pos 123))) ∷ []))) ∷ ((bDATA (mkByteString "\187")) , (MapDATA (((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 2))) ∷ []))) ∷ ((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\170")) , (iDATA (ℤ.pos 80))) ∷ []))) ∷ ((bDATA (mkByteString "\204")) , (MapDATA (((bDATA (mkByteString "\204")) , (iDATA (ℤ.pos 2))) ∷ []))) ∷ ((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\170")) , (iDATA (ℤ.pos 43))) ∷ []))) ∷ [])))))

expected-data-duplicate-currencies-merge : Result
expected-data-duplicate-currencies-merge = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-data-duplicate-currencies-merge : Set
pending-data-duplicate-currencies-merge = Pending (evalRaw test-data-duplicate-currencies-merge ≡ expected-data-duplicate-currencies-merge)
```

## data-duplicate-tokens

```
-- builtin/semantics/unValueData/data-duplicate-tokens
test-data-duplicate-tokens : Untyped
test-data-duplicate-tokens = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 100))) ∷ ((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 50))) ∷ []))) ∷ [])))))

expected-data-duplicate-tokens : Result
expected-data-duplicate-tokens = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-data-duplicate-tokens : Set
pending-data-duplicate-tokens = Pending (evalRaw test-data-duplicate-tokens ≡ expected-data-duplicate-tokens)
```

## data-empty-tokens

```
-- builtin/semantics/unValueData/data-empty-tokens
test-data-empty-tokens : Untyped
test-data-empty-tokens = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA ([]))) ∷ [])))))

expected-data-empty-tokens : Result
expected-data-empty-tokens = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-data-empty-tokens : Set
pending-data-empty-tokens = Pending (evalRaw test-data-empty-tokens ≡ expected-data-empty-tokens)
```

## data-unordered-currencies

```
-- builtin/semantics/unValueData/data-unordered-currencies
test-data-unordered-currencies : Untyped
test-data-unordered-currencies = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\187")) , (MapDATA (((bDATA (mkByteString "\170")) , (iDATA (ℤ.pos 10))) ∷ []))) ∷ ((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\204")) , (iDATA (ℤ.pos 20))) ∷ []))) ∷ [])))))

expected-data-unordered-currencies : Result
expected-data-unordered-currencies = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-data-unordered-currencies : Set
pending-data-unordered-currencies = Pending (evalRaw test-data-unordered-currencies ≡ expected-data-unordered-currencies)
```

## data-unordered-tokens

```
-- builtin/semantics/unValueData/data-unordered-tokens
test-data-unordered-tokens : Untyped
test-data-unordered-tokens = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\204")) , (iDATA (ℤ.pos 100))) ∷ ((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 50))) ∷ []))) ∷ [])))))

expected-data-unordered-tokens : Result
expected-data-unordered-tokens = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-data-unordered-tokens : Set
pending-data-unordered-tokens = Pending (evalRaw test-data-unordered-tokens ≡ expected-data-unordered-tokens)
```

## data-zero-quantity

```
-- builtin/semantics/unValueData/data-zero-quantity
test-data-zero-quantity : Untyped
test-data-zero-quantity = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 0))) ∷ ((bDATA (mkByteString "\204")) , (iDATA (ℤ.pos 100))) ∷ []))) ∷ [])))))

expected-data-zero-quantity : Result
expected-data-zero-quantity = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-data-zero-quantity : Set
pending-data-zero-quantity = Pending (evalRaw test-data-zero-quantity ≡ expected-data-zero-quantity)
```

## data-zero-sum

```
-- builtin/semantics/unValueData/data-zero-sum
test-data-zero-sum : Untyped
test-data-zero-sum = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 100))) ∷ ((bDATA (mkByteString "\187")) , (iDATA (ℤ.negsuc 99))) ∷ []))) ∷ [])))))

expected-data-zero-sum : Result
expected-data-zero-sum = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-data-zero-sum : Set
pending-data-zero-sum = Pending (evalRaw test-data-zero-sum ≡ expected-data-zero-sum)
```

## empty

```
-- builtin/semantics/unValueData/empty
test-empty : Untyped
test-empty = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA ([])))))

expected-empty : Result
expected-empty = success (UCon (tagCon value (valueFromList ([]))))

-- Pending: value constant; postulated builtin `unValueData`.
pending-empty : Set
pending-empty = Pending (evalRaw test-empty ≡ expected-empty)
```

## max-key-len

```
-- builtin/semantics/unValueData/max-key-len
test-max-key-len : Untyped
test-max-key-len = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")) , (MapDATA (((bDATA (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")) , (iDATA (ℤ.pos 1))) ∷ []))) ∷ [])))))

expected-max-key-len : Result
expected-max-key-len = success (UCon (tagCon value (valueFromList (((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (((mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL") , (ℤ.pos 1)) ∷ [])) ∷ []))))

-- Pending: bytestring inside a `data` constant; value constant; postulated builtin `unValueData`.
pending-max-key-len : Set
pending-max-key-len = Pending (evalRaw test-max-key-len ≡ expected-max-key-len)
```

## multi-currency

```
-- builtin/semantics/unValueData/multi-currency
test-multi-currency : Untyped
test-multi-currency = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\170")) , (iDATA (ℤ.pos 1))) ∷ []))) ∷ ((bDATA (mkByteString "\187")) , (MapDATA (((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 2))) ∷ []))) ∷ [])))))

expected-multi-currency : Result
expected-multi-currency = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\187") , (ℤ.pos 2)) ∷ [])) ∷ []))))

-- Pending: bytestring inside a `data` constant; value constant; postulated builtin `unValueData`.
pending-multi-currency : Set
pending-multi-currency = Pending (evalRaw test-multi-currency ≡ expected-multi-currency)
```

## multi-token

```
-- builtin/semantics/unValueData/multi-token
test-multi-token : Untyped
test-multi-token = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\170")) , (iDATA (ℤ.pos 5))) ∷ ((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 10))) ∷ []))) ∷ [])))))

expected-multi-token : Result
expected-multi-token = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 5)) ∷ ((mkByteString "\187") , (ℤ.pos 10)) ∷ [])) ∷ []))))

-- Pending: bytestring inside a `data` constant; value constant; postulated builtin `unValueData`.
pending-multi-token : Set
pending-multi-token = Pending (evalRaw test-multi-token ≡ expected-multi-token)
```

## negative-quantity

```
-- builtin/semantics/unValueData/negative-quantity
test-negative-quantity : Untyped
test-negative-quantity = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "")) , (MapDATA (((bDATA (mkByteString "")) , (iDATA (ℤ.negsuc 99))) ∷ []))) ∷ [])))))

expected-negative-quantity : Result
expected-negative-quantity = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.negsuc 99)) ∷ [])) ∷ []))))

-- Pending: bytestring inside a `data` constant; value constant; postulated builtin `unValueData`.
pending-negative-quantity : Set
pending-negative-quantity = Pending (evalRaw test-negative-quantity ≡ expected-negative-quantity)
```

## non-bytestring-currency

```
-- builtin/semantics/unValueData/non-bytestring-currency
-- Currency symbol key is I instead of B
test-non-bytestring-currency : Untyped
test-non-bytestring-currency = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((iDATA (ℤ.pos 1)) , (MapDATA (((bDATA (mkByteString "")) , (iDATA (ℤ.pos 1))) ∷ []))) ∷ [])))))

expected-non-bytestring-currency : Result
expected-non-bytestring-currency = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-non-bytestring-currency : Set
pending-non-bytestring-currency = Pending (evalRaw test-non-bytestring-currency ≡ expected-non-bytestring-currency)
```

## non-bytestring-token

```
-- builtin/semantics/unValueData/non-bytestring-token
-- Token name key is I instead of B
test-non-bytestring-token : Untyped
test-non-bytestring-token = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "")) , (MapDATA (((iDATA (ℤ.pos 1)) , (iDATA (ℤ.pos 1))) ∷ []))) ∷ [])))))

expected-non-bytestring-token : Result
expected-non-bytestring-token = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-non-bytestring-token : Set
pending-non-bytestring-token = Pending (evalRaw test-non-bytestring-token ≡ expected-non-bytestring-token)
```

## non-integer-quantity

```
-- builtin/semantics/unValueData/non-integer-quantity
-- Quantity is B instead of I
test-non-integer-quantity : Untyped
test-non-integer-quantity = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "")) , (MapDATA (((bDATA (mkByteString "")) , (bDATA (mkByteString "\255"))) ∷ []))) ∷ [])))))

expected-non-integer-quantity : Result
expected-non-integer-quantity = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-non-integer-quantity : Set
pending-non-integer-quantity = Pending (evalRaw test-non-integer-quantity ≡ expected-non-integer-quantity)
```

## non-map-bytes

```
-- builtin/semantics/unValueData/non-map-bytes
test-non-map-bytes : Untyped
test-non-map-bytes = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (bDATA (mkByteString "\255")))))

expected-non-map-bytes : Result
expected-non-map-bytes = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-non-map-bytes : Set
pending-non-map-bytes = Pending (evalRaw test-non-map-bytes ≡ expected-non-map-bytes)
```

## non-map-constr

```
-- builtin/semantics/unValueData/non-map-constr
test-non-map-constr : Untyped
test-non-map-constr = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (ConstrDATA (ℤ.pos 0) ([])))))

expected-non-map-constr : Result
expected-non-map-constr = failure

-- Pending: postulated builtin `unValueData`.
pending-non-map-constr : Set
pending-non-map-constr = Pending (evalRaw test-non-map-constr ≡ expected-non-map-constr)
```

## non-map-integer

```
-- builtin/semantics/unValueData/non-map-integer
test-non-map-integer : Untyped
test-non-map-integer = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (iDATA (ℤ.pos 42)))))

expected-non-map-integer : Result
expected-non-map-integer = failure

-- Pending: postulated builtin `unValueData`.
pending-non-map-integer : Set
pending-non-map-integer = Pending (evalRaw test-non-map-integer ≡ expected-non-map-integer)
```

## non-map-list

```
-- builtin/semantics/unValueData/non-map-list
test-non-map-list : Untyped
test-non-map-list = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (ListDATA ([])))))

expected-non-map-list : Result
expected-non-map-list = failure

-- Pending: postulated builtin `unValueData`.
pending-non-map-list : Set
pending-non-map-list = Pending (evalRaw test-non-map-list ≡ expected-non-map-list)
```

## non-map-tokens

```
-- builtin/semantics/unValueData/non-map-tokens
-- Inner value should be Map but is I
test-non-map-tokens : Untyped
test-non-map-tokens = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "")) , (iDATA (ℤ.pos 1))) ∷ [])))))

expected-non-map-tokens : Result
expected-non-map-tokens = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-non-map-tokens : Set
pending-non-map-tokens = Pending (evalRaw test-non-map-tokens ≡ expected-non-map-tokens)
```

## quantity-overflow

```
-- builtin/semantics/unValueData/quantity-overflow
-- Quantity > 2^127-1
test-quantity-overflow : Untyped
test-quantity-overflow = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "")) , (MapDATA (((bDATA (mkByteString "")) , (iDATA (ℤ.pos 170141183460469231731687303715884105728))) ∷ []))) ∷ [])))))

expected-quantity-overflow : Result
expected-quantity-overflow = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-quantity-overflow : Set
pending-quantity-overflow = Pending (evalRaw test-quantity-overflow ≡ expected-quantity-overflow)
```

## quantity-underflow

```
-- builtin/semantics/unValueData/quantity-underflow
-- Quantity < -2^127
test-quantity-underflow : Untyped
test-quantity-underflow = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "")) , (MapDATA (((bDATA (mkByteString "")) , (iDATA (ℤ.negsuc 170141183460469231731687303715884105728))) ∷ []))) ∷ [])))))

expected-quantity-underflow : Result
expected-quantity-underflow = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-quantity-underflow : Set
pending-quantity-underflow = Pending (evalRaw test-quantity-underflow ≡ expected-quantity-underflow)
```

## roundtrip-from-data

```
-- builtin/semantics/unValueData/roundtrip-from-data
test-roundtrip-from-data : Untyped
test-roundtrip-from-data = (UApp (UBuiltin valueData) (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 100))) ∷ []))) ∷ []))))))

expected-roundtrip-from-data : Result
expected-roundtrip-from-data = success (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 100))) ∷ []))) ∷ []))))

-- Pending: bytestring inside a `data` constant; postulated builtin `valueData`; postulated builtin `unValueData`.
pending-roundtrip-from-data : Set
pending-roundtrip-from-data = Pending (evalRaw test-roundtrip-from-data ≡ expected-roundtrip-from-data)
```

## single-entry

```
-- builtin/semantics/unValueData/single-entry
test-single-entry : Untyped
test-single-entry = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "")) , (MapDATA (((bDATA (mkByteString "")) , (iDATA (ℤ.pos 1))) ∷ []))) ∷ [])))))

expected-single-entry : Result
expected-single-entry = success (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ []))))

-- Pending: bytestring inside a `data` constant; value constant; postulated builtin `unValueData`.
pending-single-entry : Set
pending-single-entry = Pending (evalRaw test-single-entry ≡ expected-single-entry)
```

## token-key-too-long

```
-- builtin/semantics/unValueData/token-key-too-long
-- Token name with 33 bytes (> maxKeyLen)
test-token-key-too-long : Untyped
test-token-key-too-long = (UApp (UBuiltin unValueData) (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "")) , (MapDATA (((bDATA (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")) , (iDATA (ℤ.pos 1))) ∷ []))) ∷ [])))))

expected-token-key-too-long : Result
expected-token-key-too-long = failure

-- Pending: bytestring inside a `data` constant; postulated builtin `unValueData`.
pending-token-key-too-long : Set
pending-token-key-too-long = Pending (evalRaw test-token-key-too-long ≡ expected-token-key-too-long)
```
