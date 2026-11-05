---
title: Conformance.Builtin.Semantics.LessThanEqualsByteString
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
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/lessThanEqualsByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.LessThanEqualsByteString where

open import Conformance.Eval
```

## lessThanEqualsByteString-00

```
-- builtin/semantics/lessThanEqualsByteString/lessThanEqualsByteString-00
test-lessThanEqualsByteString-00 : Untyped
<<<<<<< HEAD
test-lessThanEqualsByteString-00 = (UApp (UApp (UBuiltin lessThanEqualsByteString) (UCon (tagCon bytestring (mkByteString "00ff")))) (UCon (tagCon bytestring (mkByteString "00"))))
=======
test-lessThanEqualsByteString-00 = (UApp (UApp (UBuiltin lessThanEqualsByteString) (UCon (tagCon bytestring (mkByteString "\NUL\255")))) (UCon (tagCon bytestring (mkByteString "\NUL"))))
>>>>>>> origin/master

expected-lessThanEqualsByteString-00 : Result
expected-lessThanEqualsByteString-00 = success (UCon (tagCon bool false))

<<<<<<< HEAD
_ : evalRaw test-lessThanEqualsByteString-00 ≡ expected-lessThanEqualsByteString-00
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `lessThanEqualsByteString`.
pending-lessThanEqualsByteString-00 : Set
pending-lessThanEqualsByteString-00 = Pending (evalRaw test-lessThanEqualsByteString-00 ≡ expected-lessThanEqualsByteString-00)
>>>>>>> origin/master
```

## lessThanEqualsByteString-01

```
-- builtin/semantics/lessThanEqualsByteString/lessThanEqualsByteString-01
test-lessThanEqualsByteString-01 : Untyped
<<<<<<< HEAD
test-lessThanEqualsByteString-01 = (UApp (UApp (UBuiltin lessThanEqualsByteString) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6964")))) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965"))))
=======
test-lessThanEqualsByteString-01 = (UApp (UApp (UBuiltin lessThanEqualsByteString) (UCon (tagCon bytestring (mkByteString "TheCakeIsALid")))) (UCon (tagCon bytestring (mkByteString "TheCakeIsALie"))))
>>>>>>> origin/master

expected-lessThanEqualsByteString-01 : Result
expected-lessThanEqualsByteString-01 = success (UCon (tagCon bool true))

<<<<<<< HEAD
_ : evalRaw test-lessThanEqualsByteString-01 ≡ expected-lessThanEqualsByteString-01
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `lessThanEqualsByteString`.
pending-lessThanEqualsByteString-01 : Set
pending-lessThanEqualsByteString-01 = Pending (evalRaw test-lessThanEqualsByteString-01 ≡ expected-lessThanEqualsByteString-01)
>>>>>>> origin/master
```

## lessThanEqualsByteString-02

```
-- builtin/semantics/lessThanEqualsByteString/lessThanEqualsByteString-02
test-lessThanEqualsByteString-02 : Untyped
<<<<<<< HEAD
test-lessThanEqualsByteString-02 = (UApp (UApp (UBuiltin lessThanEqualsByteString) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6966")))) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965"))))
=======
test-lessThanEqualsByteString-02 = (UApp (UApp (UBuiltin lessThanEqualsByteString) (UCon (tagCon bytestring (mkByteString "TheCakeIsALif")))) (UCon (tagCon bytestring (mkByteString "TheCakeIsALie"))))
>>>>>>> origin/master

expected-lessThanEqualsByteString-02 : Result
expected-lessThanEqualsByteString-02 = success (UCon (tagCon bool false))

<<<<<<< HEAD
_ : evalRaw test-lessThanEqualsByteString-02 ≡ expected-lessThanEqualsByteString-02
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `lessThanEqualsByteString`.
pending-lessThanEqualsByteString-02 : Set
pending-lessThanEqualsByteString-02 = Pending (evalRaw test-lessThanEqualsByteString-02 ≡ expected-lessThanEqualsByteString-02)
>>>>>>> origin/master
```

## lessThanEqualsByteString-03

```
-- builtin/semantics/lessThanEqualsByteString/lessThanEqualsByteString-03
test-lessThanEqualsByteString-03 : Untyped
<<<<<<< HEAD
test-lessThanEqualsByteString-03 = (UApp (UApp (UBuiltin lessThanEqualsByteString) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965")))) (UCon (tagCon bytestring (mkByteString "54686543616b654973414c6965"))))
=======
test-lessThanEqualsByteString-03 = (UApp (UApp (UBuiltin lessThanEqualsByteString) (UCon (tagCon bytestring (mkByteString "TheCakeIsALie")))) (UCon (tagCon bytestring (mkByteString "TheCakeIsALie"))))
>>>>>>> origin/master

expected-lessThanEqualsByteString-03 : Result
expected-lessThanEqualsByteString-03 = success (UCon (tagCon bool true))

<<<<<<< HEAD
_ : evalRaw test-lessThanEqualsByteString-03 ≡ expected-lessThanEqualsByteString-03
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `lessThanEqualsByteString`.
pending-lessThanEqualsByteString-03 : Set
pending-lessThanEqualsByteString-03 = Pending (evalRaw test-lessThanEqualsByteString-03 ≡ expected-lessThanEqualsByteString-03)
>>>>>>> origin/master
```
