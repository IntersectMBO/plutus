---
title: Conformance.Builtin.Semantics.DecodeUtf8
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/decodeUtf8`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.DecodeUtf8 where

open import Conformance.Eval
```

## decodeUtf8-invalid

```
-- builtin/semantics/decodeUtf8/decodeUtf8-invalid
-- invalid utf8
test-decodeUtf8-invalid : Untyped
test-decodeUtf8-invalid = (UApp (UBuiltin decodeUtf8) (UCon (tagCon bytestring (mkByteString "\163"))))

expected-decodeUtf8-invalid : Result
expected-decodeUtf8-invalid = failure

-- Pending: bytestring constant; postulated builtin `decodeUtf8`.
pending-decodeUtf8-invalid : Set
pending-decodeUtf8-invalid = Pending (evalRaw test-decodeUtf8-invalid ≡ expected-decodeUtf8-invalid)
```

## decodeUtf8-ok

```
-- builtin/semantics/decodeUtf8/decodeUtf8-ok
test-decodeUtf8-ok : Untyped
test-decodeUtf8-ok = (UApp (UBuiltin decodeUtf8) (UCon (tagCon bytestring (mkByteString "Ola"))))

expected-decodeUtf8-ok : Result
expected-decodeUtf8-ok = success (UCon (tagCon string "Ola"))

-- Pending: bytestring constant; postulated builtin `decodeUtf8`.
pending-decodeUtf8-ok : Set
pending-decodeUtf8-ok = Pending (evalRaw test-decodeUtf8-ok ≡ expected-decodeUtf8-ok)
```
