---
title: Conformance.Builtin.Semantics.IndexByteString
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/indexByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.IndexByteString where

open import Conformance.Eval
```

## indexByteString-01

```
-- builtin/semantics/indexByteString/indexByteString-01
test-indexByteString-01 : Untyped
test-indexByteString-01 = (UApp (UApp (UBuiltin indexByteString) (UCon (tagCon bytestring (mkByteString "00ffaa")))) (UCon (tagCon integer (ℤ.pos 1))))

expected-indexByteString-01 : Result
expected-indexByteString-01 = success (UCon (tagCon integer (ℤ.pos 255)))

_ : evalRaw test-indexByteString-01 ≡ expected-indexByteString-01
_ = refl
```

## indexByteStringOOB

```
-- builtin/semantics/indexByteString/indexByteStringOOB
test-indexByteStringOOB : Untyped
test-indexByteStringOOB = (UApp (UApp (UBuiltin indexByteString) (UCon (tagCon bytestring (mkByteString "00")))) (UCon (tagCon integer (ℤ.pos 1))))

expected-indexByteStringOOB : Result
expected-indexByteStringOOB = failure

_ : evalRaw test-indexByteStringOOB ≡ expected-indexByteStringOOB
_ = refl
```

## indexByteStringOverflow

```
-- builtin/semantics/indexByteString/indexByteStringOverflow
-- this is different than out-of-bounds error, the index argument overflow'ed the maxBound :: Int64
-- same error would happen when underflow'ing the minBound :: Int64
test-indexByteStringOverflow : Untyped
test-indexByteStringOverflow = (UApp (UApp (UBuiltin indexByteString) (UCon (tagCon bytestring (mkByteString "00")))) (UCon (tagCon integer (ℤ.pos 9223372036854775808))))

expected-indexByteStringOverflow : Result
expected-indexByteStringOverflow = failure

_ : evalRaw test-indexByteStringOverflow ≡ expected-indexByteStringOverflow
_ = refl
```
