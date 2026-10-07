---
title: Conformance.Builtin.Semantics.UnIData
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/unIData`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.UnIData where

open import Conformance.Eval
```

## unIData-01

```
-- builtin/semantics/unIData/unIData-01
test-unIData-01 : Untyped
test-unIData-01 = (UApp (UBuiltin unIData) (UCon (tagCon pdata (iDATA (ℤ.negsuc 123456788)))))

expected-unIData-01 : Result
expected-unIData-01 = success (UCon (tagCon integer (ℤ.negsuc 123456788)))

_ : evalRaw test-unIData-01 ≡ expected-unIData-01
_ = refl
```

## unIData-fail

```
-- builtin/semantics/unIData/unIData-fail
test-unIData-fail : Untyped
test-unIData-fail = (UApp (UBuiltin unIData) (UCon (tagCon pdata (bDATA (mkByteString "\175\NUL")))))

expected-unIData-fail : Result
expected-unIData-fail = failure

-- Pending: bytestring inside a `data` constant.
pending-unIData-fail : Set
pending-unIData-fail = Pending (evalRaw test-unIData-fail ≡ expected-unIData-fail)
```
