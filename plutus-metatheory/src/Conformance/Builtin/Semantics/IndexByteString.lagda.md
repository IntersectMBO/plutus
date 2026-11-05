---
title: Conformance.Builtin.Semantics.IndexByteString
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
<<<<<<< HEAD
test-indexByteString-01 = (UApp (UApp (UBuiltin indexByteString) (UCon (tagCon bytestring (mkByteString "00ffaa")))) (UCon (tagCon integer (ℤ.pos 1))))
=======
test-indexByteString-01 = (UApp (UApp (UBuiltin indexByteString) (UCon (tagCon bytestring (mkByteString "\NUL\255\170")))) (UCon (tagCon integer (ℤ.pos 1))))
>>>>>>> origin/master

expected-indexByteString-01 : Result
expected-indexByteString-01 = success (UCon (tagCon integer (ℤ.pos 255)))

<<<<<<< HEAD
_ : evalRaw test-indexByteString-01 ≡ expected-indexByteString-01
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `indexByteString`.
pending-indexByteString-01 : Set
pending-indexByteString-01 = Pending (evalRaw test-indexByteString-01 ≡ expected-indexByteString-01)
>>>>>>> origin/master
```

## indexByteStringOOB

```
-- builtin/semantics/indexByteString/indexByteStringOOB
test-indexByteStringOOB : Untyped
<<<<<<< HEAD
test-indexByteStringOOB = (UApp (UApp (UBuiltin indexByteString) (UCon (tagCon bytestring (mkByteString "00")))) (UCon (tagCon integer (ℤ.pos 1))))
=======
test-indexByteStringOOB = (UApp (UApp (UBuiltin indexByteString) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon integer (ℤ.pos 1))))
>>>>>>> origin/master

expected-indexByteStringOOB : Result
expected-indexByteStringOOB = failure

<<<<<<< HEAD
_ : evalRaw test-indexByteStringOOB ≡ expected-indexByteStringOOB
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `indexByteString`.
pending-indexByteStringOOB : Set
pending-indexByteStringOOB = Pending (evalRaw test-indexByteStringOOB ≡ expected-indexByteStringOOB)
>>>>>>> origin/master
```

## indexByteStringOverflow

```
-- builtin/semantics/indexByteString/indexByteStringOverflow
-- this is different than out-of-bounds error, the index argument overflow'ed the maxBound :: Int64
-- same error would happen when underflow'ing the minBound :: Int64
test-indexByteStringOverflow : Untyped
<<<<<<< HEAD
test-indexByteStringOverflow = (UApp (UApp (UBuiltin indexByteString) (UCon (tagCon bytestring (mkByteString "00")))) (UCon (tagCon integer (ℤ.pos 9223372036854775808))))
=======
test-indexByteStringOverflow = (UApp (UApp (UBuiltin indexByteString) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon integer (ℤ.pos 9223372036854775808))))
>>>>>>> origin/master

expected-indexByteStringOverflow : Result
expected-indexByteStringOverflow = failure

<<<<<<< HEAD
_ : evalRaw test-indexByteStringOverflow ≡ expected-indexByteStringOverflow
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `indexByteString`.
pending-indexByteStringOverflow : Set
pending-indexByteStringOverflow = Pending (evalRaw test-indexByteStringOverflow ≡ expected-indexByteStringOverflow)
>>>>>>> origin/master
```
