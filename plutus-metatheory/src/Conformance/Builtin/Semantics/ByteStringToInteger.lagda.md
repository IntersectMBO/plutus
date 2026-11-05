---
title: Conformance.Builtin.Semantics.ByteStringToInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
<<<<<<< HEAD
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
=======
     Regenerate with `generate-agda-typecheck-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-typecheck-conformance` from the
>>>>>>> origin/master
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
<<<<<<< HEAD
test-both-endian = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "92828b9d9e097a23ef34ba5522ee67"))))) (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "67ee2255ba34ef237a099e9d8b8292")))))
=======
test-both-endian = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\146\130\139\157\158\tz#\239\&4\186U\"\238g"))))) (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "g\238\"U\186\&4\239#z\t\158\157\139\130\146")))))
>>>>>>> origin/master

expected-both-endian : Result
expected-both-endian = success (UCon (tagCon bool true))

<<<<<<< HEAD
_ : evalRaw test-both-endian ≡ expected-both-endian
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `byteStringToInteger`.
pending-both-endian : Set
pending-both-endian = Pending (evalRaw test-both-endian ≡ expected-both-endian)
>>>>>>> origin/master
```
