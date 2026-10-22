---
title: Conformance.Builtin.Semantics.ByteStringToInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/byteStringToInteger`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ByteStringToInteger where

open import Conformance.Eval
```

## both-endian

```
-- builtin/semantics/byteStringToInteger/both-endian
-- Check that the big-endian decoding of a bytestring is the same as the
-- little-endian decoding of its reverse.
test-both-endian : Untyped
test-both-endian = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "92828b9d9e097a23ef34ba5522ee67"))))) (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "67ee2255ba34ef237a099e9d8b8292")))))

expected-both-endian : Result
expected-both-endian = success (UCon (tagCon bool true))

_ : evalRaw test-both-endian ≡ expected-both-endian
_ = refl
```
