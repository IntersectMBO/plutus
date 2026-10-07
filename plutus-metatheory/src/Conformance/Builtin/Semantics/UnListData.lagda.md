---
title: Conformance.Builtin.Semantics.UnListData
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/unListData`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.UnListData where

open import Conformance.Eval
```

## unListData-01

```
-- builtin/semantics/unListData/unListData-01
test-unListData-01 : Untyped
test-unListData-01 = (UApp (UBuiltin unListData) (UCon (tagCon pdata (ListDATA ((iDATA (ℤ.pos 0)) ∷ (iDATA (ℤ.pos 1)) ∷ [])))))

expected-unListData-01 : Result
expected-unListData-01 = success (UCon (tagCon (list pdata) ((iDATA (ℤ.pos 0)) ∷ (iDATA (ℤ.pos 1)) ∷ [])))

_ : evalRaw test-unListData-01 ≡ expected-unListData-01
_ = refl
```

## unListData-fail

```
-- builtin/semantics/unListData/unListData-fail
test-unListData-fail : Untyped
test-unListData-fail = (UApp (UBuiltin unListData) (UCon (tagCon pdata (bDATA (mkByteString "\175\NUL")))))

expected-unListData-fail : Result
expected-unListData-fail = failure

-- Pending: bytestring inside a `data` constant.
pending-unListData-fail : Set
pending-unListData-fail = Pending (evalRaw test-unListData-fail ≡ expected-unListData-fail)
```
