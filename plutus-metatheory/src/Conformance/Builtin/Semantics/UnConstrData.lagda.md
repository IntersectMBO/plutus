---
title: Conformance.Builtin.Semantics.UnConstrData
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/unConstrData`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.UnConstrData where

open import Conformance.Eval
```

## unConstrData-01

```
-- builtin/semantics/unConstrData/unConstrData-01
test-unConstrData-01 : Untyped
test-unConstrData-01 = (UApp (UBuiltin unConstrData) (UCon (tagCon pdata (ConstrDATA (ℤ.pos 1278) ((bDATA (mkByteString "\255\&1")) ∷ (iDATA (ℤ.negsuc 7971)) ∷ (ListDATA ((ListDATA ([])) ∷ [])) ∷ [])))))

expected-unConstrData-01 : Result
expected-unConstrData-01 = success (UCon (tagCon (pair integer (list pdata)) ((ℤ.pos 1278) , ((bDATA (mkByteString "\255\&1")) ∷ (iDATA (ℤ.negsuc 7971)) ∷ (ListDATA ((ListDATA ([])) ∷ [])) ∷ []))))

-- Pending: bytestring inside a `data` constant.
pending-unConstrData-01 : Set
pending-unConstrData-01 = Pending (evalRaw test-unConstrData-01 ≡ expected-unConstrData-01)
```

## unConstrData-fail

```
-- builtin/semantics/unConstrData/unConstrData-fail
test-unConstrData-fail : Untyped
test-unConstrData-fail = (UApp (UBuiltin unConstrData) (UCon (tagCon pdata (bDATA (mkByteString "\175\NUL")))))

expected-unConstrData-fail : Result
expected-unConstrData-fail = failure

-- Pending: bytestring inside a `data` constant.
pending-unConstrData-fail : Set
pending-unConstrData-fail = Pending (evalRaw test-unConstrData-fail ≡ expected-unConstrData-fail)
```
