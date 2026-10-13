---
title: Conformance.Builtin.Semantics.ByteStringToInteger.LittleEndian
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/byteStringToInteger/little-endian`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ByteStringToInteger.LittleEndian where

open import Conformance.Eval
```

## all-zeros

```
-- builtin/semantics/byteStringToInteger/little-endian/all-zeros
-- A bytestring consisting entirely of zeros decodes to 0.
test-all-zeros : Untyped
test-all-zeros = (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "00000000000000000000000000"))))

expected-all-zeros : Result
expected-all-zeros = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-all-zeros ≡ expected-all-zeros
_ = refl
```

## correct-output

```
-- builtin/semantics/byteStringToInteger/little-endian/correct-output
-- Check that a particular bytestring decodes to the expected integer.
test-correct-output : Untyped
test-correct-output = (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "123456abcdef"))))

expected-correct-output : Result
expected-correct-output = success (UCon (tagCon integer (ℤ.pos 263666621887506)))

_ : evalRaw test-correct-output ≡ expected-correct-output
_ = refl
```

## empty

```
-- builtin/semantics/byteStringToInteger/little-endian/empty
-- The empty bytestring decodes to 0
test-empty : Untyped
test-empty = (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString ""))))

expected-empty : Result
expected-empty = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-empty ≡ expected-empty
_ = refl
```

## trailing-zeros

```
-- builtin/semantics/byteStringToInteger/little-endian/trailing-zeros
-- Check that trailing zeros don't affect the result of a little-endian decoding.
test-trailing-zeros : Untyped
test-trailing-zeros = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "123456abcdef"))))) (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "123456abcdef0000000000000000")))))

expected-trailing-zeros : Result
expected-trailing-zeros = success (UCon (tagCon bool true))

_ : evalRaw test-trailing-zeros ≡ expected-trailing-zeros
_ = refl
```
