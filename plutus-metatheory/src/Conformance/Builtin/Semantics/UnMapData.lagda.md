---
title: Conformance.Builtin.Semantics.UnMapData
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/unMapData`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.UnMapData where

open import Conformance.Eval
```

## unMapData-01

```
-- builtin/semantics/unMapData/unMapData-01
test-unMapData-01 : Untyped
test-unMapData-01 = (UApp (UBuiltin unMapData) (UCon (tagCon pdata (MapDATA (((iDATA (ℤ.pos 0)) , (iDATA (ℤ.pos 1))) ∷ [])))))

expected-unMapData-01 : Result
expected-unMapData-01 = success (UCon (tagCon (list (pair pdata pdata)) (((iDATA (ℤ.pos 0)) , (iDATA (ℤ.pos 1))) ∷ [])))

_ : evalRaw test-unMapData-01 ≡ expected-unMapData-01
_ = refl
```

## unMapData-fail

```
-- builtin/semantics/unMapData/unMapData-fail
test-unMapData-fail : Untyped
test-unMapData-fail = (UApp (UBuiltin unMapData) (UCon (tagCon pdata (bDATA (mkByteString "\175\NUL")))))

expected-unMapData-fail : Result
expected-unMapData-fail = failure

-- Pending: bytestring inside a `data` constant.
pending-unMapData-fail : Set
pending-unMapData-fail = Pending (evalRaw test-unMapData-fail ≡ expected-unMapData-fail)
```
