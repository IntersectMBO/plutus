---
title: Conformance.Builtin.Semantics.LookupCoin
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/lookupCoin`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.LookupCoin where

open import Conformance.Eval
```

## absent

```
-- builtin/semantics/lookupCoin/absent
test-absent : Untyped
test-absent = (UApp (UApp (UApp (UBuiltin lookupCoin) (UCon (tagCon bytestring (mkByteString "\170")))) (UCon (tagCon bytestring (mkByteString "\187")))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 100)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-absent : Result
expected-absent = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: bytestring constant; value constant; postulated builtin `lookupCoin`.
pending-absent : Set
pending-absent = Pending (evalRaw test-absent ≡ expected-absent)
```

## present

```
-- builtin/semantics/lookupCoin/present
test-present : Untyped
test-present = (UApp (UApp (UApp (UBuiltin lookupCoin) (UCon (tagCon bytestring (mkByteString "\170")))) (UCon (tagCon bytestring (mkByteString "\170")))) (UCon (tagCon value (valueFromList (((mkByteString "\170") , (((mkByteString "\170") , (ℤ.pos 100)) ∷ [])) ∷ ((mkByteString "\187") , (((mkByteString "\170") , (ℤ.pos 1)) ∷ [])) ∷ [])))))

expected-present : Result
expected-present = success (UCon (tagCon integer (ℤ.pos 100)))

-- Pending: bytestring constant; value constant; postulated builtin `lookupCoin`.
pending-present : Set
pending-present = Pending (evalRaw test-present ≡ expected-present)
```
