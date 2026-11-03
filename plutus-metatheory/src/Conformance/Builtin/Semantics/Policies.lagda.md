---
title: Conformance.Builtin.Semantics.Policies
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-typecheck-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-typecheck-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/policies`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.Policies where

open import Conformance.Eval
```

## policies-01

```
-- builtin/semantics/policies/policies-01
-- Empty Value
test-policies-01 : Untyped
test-policies-01 = (UApp (UBuiltin policies) (UCon (tagCon value (valueFromList ([])))))

expected-policies-01 : Result
expected-policies-01 = success (UCon (tagCon (list bytestring) ([])))

-- Pending: value constant; postulated builtin `policies`.
pending-policies-01 : Set
pending-policies-01 = Pending (evalRaw test-policies-01 ≡ expected-policies-01)
```

## policies-02

```
-- builtin/semantics/policies/policies-02
-- Single asset
test-policies-02 : Untyped
test-policies-02 = (UApp (UBuiltin policies) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\SOH") , (ℤ.pos 42)) ∷ [])) ∷ [])))))

expected-policies-02 : Result
expected-policies-02 = success (UCon (tagCon (list bytestring) ((mkByteString "\170") ∷ [])))

-- Pending: value constant; bytestring constant; postulated builtin `policies`.
pending-policies-02 : Set
pending-policies-02 = Pending (evalRaw test-policies-02 ≡ expected-policies-02)
```

## policies-03

```
-- builtin/semantics/policies/policies-03
-- Lovelace only
test-policies-03 : Untyped
test-policies-03 = (UApp (UBuiltin policies) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1000000)) ∷ [])) ∷ [])))))

expected-policies-03 : Result
expected-policies-03 = success (UCon (tagCon (list bytestring) ((mkByteString "") ∷ [])))

-- Pending: value constant; bytestring constant; postulated builtin `policies`.
pending-policies-03 : Set
pending-policies-03 = Pending (evalRaw test-policies-03 ≡ expected-policies-03)
```

## policies-04

```
-- builtin/semantics/policies/policies-04
-- Multiple assets per policy
test-policies-04 : Untyped
test-policies-04 = (UApp (UBuiltin policies) (UCon (tagCon value (valueFromList (((mkByteString "") , (((mkByteString "") , (ℤ.pos 1000000)) ∷ [])) ∷ ((mkByteString "\170") , (((mkByteString "\SOH") , (ℤ.pos 5)) ∷ ((mkByteString "\STX") , (ℤ.negsuc 6)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "") , (ℤ.negsuc 1)) ∷ ((mkByteString "\255") , (ℤ.pos 9)) ∷ [])) ∷ ((mkByteString "\204") , (((mkByteString "\SOH") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-policies-04 : Result
expected-policies-04 = success (UCon (tagCon (list bytestring) ((mkByteString "") ∷ (mkByteString "\170") ∷ (mkByteString "\187") ∷ (mkByteString "\204") ∷ [])))

-- Pending: value constant; bytestring constant; postulated builtin `policies`.
pending-policies-04 : Set
pending-policies-04 = Pending (evalRaw test-policies-04 ≡ expected-policies-04)
```

## policies-05

```
-- builtin/semantics/policies/policies-05
-- Bytewise ordering and maximum keys
test-policies-05 : Untyped
test-policies-05 = (UApp (UBuiltin policies) (UCon (tagCon value (valueFromList (((mkByteString "\NUL") , (((mkByteString "") , (ℤ.negsuc 170141183460469231731687303715884105727)) ∷ [])) ∷ ((mkByteString "\NUL\NUL") , (((mkByteString "\SOH") , (ℤ.pos 170141183460469231731687303715884105727)) ∷ [])) ∷ ((mkByteString "\SOH") , (((mkByteString "") , (ℤ.pos 1)) ∷ [])) ∷ ((mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255") , (((mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255") , (ℤ.negsuc 0)) ∷ [])) ∷ [])))))

expected-policies-05 : Result
expected-policies-05 = success (UCon (tagCon (list bytestring) ((mkByteString "\NUL") ∷ (mkByteString "\NUL\NUL") ∷ (mkByteString "\SOH") ∷ (mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255") ∷ [])))

-- Pending: value constant; bytestring constant; postulated builtin `policies`.
pending-policies-05 : Set
pending-policies-05 = Pending (evalRaw test-policies-05 ≡ expected-policies-05)
```
