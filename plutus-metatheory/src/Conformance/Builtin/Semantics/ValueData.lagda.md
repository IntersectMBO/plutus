---
title: Conformance.Builtin.Semantics.ValueData
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/valueData`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ValueData where

open import Conformance.Eval
```

## empty

```
-- builtin/semantics/valueData/empty
test-empty : Untyped
test-empty = (UApp (UBuiltin valueData) (UCon (tagCon value (valueFromList ([])))))

expected-empty : Result
expected-empty = success (UCon (tagCon pdata (MapDATA ([]))))

-- Pending: value constant; postulated builtin `valueData`.
pending-empty : Set
pending-empty = Pending (evalRaw test-empty ≡ expected-empty)
```

## multi-currency

```
-- builtin/semantics/valueData/multi-currency
test-multi-currency : Untyped
test-multi-currency = (UApp (UBuiltin valueData) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\187") , (ℤ.pos 2)) ∷ [])) ∷ [])))))

expected-multi-currency : Result
expected-multi-currency = success (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\170")) , (iDATA (ℤ.pos 1))) ∷ []))) ∷ ((bDATA (mkByteString "\187")) , (MapDATA (((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 2))) ∷ []))) ∷ []))))

-- Pending: value constant; bytestring inside a `data` constant; postulated builtin `valueData`.
pending-multi-currency : Set
pending-multi-currency = Pending (evalRaw test-multi-currency ≡ expected-multi-currency)
```

## multi-token

```
-- builtin/semantics/valueData/multi-token
test-multi-token : Untyped
test-multi-token = (UApp (UBuiltin valueData) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 5)) ∷ ((mkByteString "\187") , (ℤ.pos 10)) ∷ [])) ∷ [])))))

expected-multi-token : Result
expected-multi-token = success (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "\170")) , (MapDATA (((bDATA (mkByteString "\170")) , (iDATA (ℤ.pos 5))) ∷ ((bDATA (mkByteString "\187")) , (iDATA (ℤ.pos 10))) ∷ []))) ∷ []))))

-- Pending: value constant; bytestring inside a `data` constant; postulated builtin `valueData`.
pending-multi-token : Set
pending-multi-token = Pending (evalRaw test-multi-token ≡ expected-multi-token)
```

## negative-quantity

```
-- builtin/semantics/valueData/negative-quantity
test-negative-quantity : Untyped
test-negative-quantity = (UApp (UBuiltin valueData) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.negsuc 99)) ∷ [])) ∷ [])))))

expected-negative-quantity : Result
expected-negative-quantity = success (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "")) , (MapDATA (((bDATA (mkByteString "")) , (iDATA (ℤ.negsuc 99))) ∷ []))) ∷ []))))

-- Pending: value constant; bytestring inside a `data` constant; postulated builtin `valueData`.
pending-negative-quantity : Set
pending-negative-quantity = Pending (evalRaw test-negative-quantity ≡ expected-negative-quantity)
```

## roundtrip-from-value

```
-- builtin/semantics/valueData/roundtrip-from-value
test-roundtrip-from-value : Untyped
test-roundtrip-from-value = (UApp (UBuiltin unValueData) (UApp (UBuiltin valueData) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\187") , (ℤ.pos 100)) ∷ [])) ∷ []))))))

expected-roundtrip-from-value : Result
expected-roundtrip-from-value = success (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\187") , (ℤ.pos 100)) ∷ [])) ∷ []))))

-- Pending: value constant; postulated builtin `unValueData`; postulated builtin `valueData`.
pending-roundtrip-from-value : Set
pending-roundtrip-from-value = Pending (evalRaw test-roundtrip-from-value ≡ expected-roundtrip-from-value)
```

## single-entry

```
-- builtin/semantics/valueData/single-entry
test-single-entry : Untyped
test-single-entry = (UApp (UBuiltin valueData) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-single-entry : Result
expected-single-entry = success (UCon (tagCon pdata (MapDATA (((bDATA (mkByteString "")) , (MapDATA (((bDATA (mkByteString "")) , (iDATA (ℤ.pos 1))) ∷ []))) ∷ []))))

-- Pending: value constant; bytestring inside a `data` constant; postulated builtin `valueData`.
pending-single-entry : Set
pending-single-entry = Pending (evalRaw test-single-entry ≡ expected-single-entry)
```
