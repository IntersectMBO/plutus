---
title: Conformance.Builtin.Semantics.ByteStringToInteger.LittleEndian
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

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
test-all-zeros = (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))

expected-all-zeros : Result
expected-all-zeros = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: bytestring constant; postulated builtin `byteStringToInteger`.
pending-all-zeros : Set
pending-all-zeros = Pending (evalRaw test-all-zeros ≡ expected-all-zeros)
```

## correct-output

```
-- builtin/semantics/byteStringToInteger/little-endian/correct-output
-- Check that a particular bytestring decodes to the expected integer.
test-correct-output : Untyped
test-correct-output = (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\DC24V\171\205\239"))))

expected-correct-output : Result
expected-correct-output = success (UCon (tagCon integer (ℤ.pos 263666621887506)))

-- Pending: bytestring constant; postulated builtin `byteStringToInteger`.
pending-correct-output : Set
pending-correct-output = Pending (evalRaw test-correct-output ≡ expected-correct-output)
```

## empty

```
-- builtin/semantics/byteStringToInteger/little-endian/empty
-- The empty bytestring decodes to 0
test-empty : Untyped
test-empty = (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString ""))))

expected-empty : Result
expected-empty = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: bytestring constant; postulated builtin `byteStringToInteger`.
pending-empty : Set
pending-empty = Pending (evalRaw test-empty ≡ expected-empty)
```

## trailing-zeros

```
-- builtin/semantics/byteStringToInteger/little-endian/trailing-zeros
-- Check that trailing zeros don't affect the result of a little-endian decoding.
test-trailing-zeros : Untyped
test-trailing-zeros = (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\DC24V\171\205\239"))))) (UApp (UApp (UBuiltin byteStringToInteger) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\DC24V\171\205\239\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))))

expected-trailing-zeros : Result
expected-trailing-zeros = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `byteStringToInteger`.
pending-trailing-zeros : Set
pending-trailing-zeros = Pending (evalRaw test-trailing-zeros ≡ expected-trailing-zeros)
```
