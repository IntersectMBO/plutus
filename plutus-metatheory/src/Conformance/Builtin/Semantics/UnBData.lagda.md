---
title: Conformance.Builtin.Semantics.UnBData
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/unBData`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.UnBData where

open import Conformance.Eval
```

## unBData-01

```
-- builtin/semantics/unBData/unBData-01
test-unBData-01 : Untyped
test-unBData-01 = (UApp (UBuiltin unBData) (UCon (tagCon pdata (bDATA (mkByteString "\175\NUL")))))

expected-unBData-01 : Result
expected-unBData-01 = success (UCon (tagCon bytestring (mkByteString "\175\NUL")))

-- Pending: bytestring inside a `data` constant; bytestring constant.
pending-unBData-01 : Set
pending-unBData-01 = Pending (evalRaw test-unBData-01 ≡ expected-unBData-01)
```

## unBData-fail

```
-- builtin/semantics/unBData/unBData-fail
test-unBData-fail : Untyped
test-unBData-fail = (UApp (UBuiltin unBData) (UCon (tagCon pdata (iDATA (ℤ.pos 0)))))

expected-unBData-fail : Result
expected-unBData-fail = failure

_ : evalRaw test-unBData-fail ≡ expected-unBData-fail
_ = refl
```
