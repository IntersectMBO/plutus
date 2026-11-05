---
title: Conformance.Builtin.Semantics.FindFirstSetBit
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
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/findFirstSetBit`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.FindFirstSetBit where

open import Conformance.Eval
```

## case-01

```
-- builtin/semantics/findFirstSetBit/case-01
test-case-01 : Untyped
test-case-01 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString ""))))

expected-case-01 : Result
expected-case-01 = success (UCon (tagCon integer (ℤ.negsuc 0)))

<<<<<<< HEAD
_ : evalRaw test-case-01 ≡ expected-case-01
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `findFirstSetBit`.
pending-case-01 : Set
pending-case-01 = Pending (evalRaw test-case-01 ≡ expected-case-01)
>>>>>>> origin/master
```

## case-02

```
-- builtin/semantics/findFirstSetBit/case-02
test-case-02 : Untyped
<<<<<<< HEAD
test-case-02 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString "0000"))))
=======
test-case-02 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString "\NUL\NUL"))))
>>>>>>> origin/master

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon integer (ℤ.negsuc 0)))

<<<<<<< HEAD
_ : evalRaw test-case-02 ≡ expected-case-02
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `findFirstSetBit`.
pending-case-02 : Set
pending-case-02 = Pending (evalRaw test-case-02 ≡ expected-case-02)
>>>>>>> origin/master
```

## case-03

```
-- builtin/semantics/findFirstSetBit/case-03
test-case-03 : Untyped
<<<<<<< HEAD
test-case-03 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString "0002"))))
=======
test-case-03 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString "\NUL\STX"))))
>>>>>>> origin/master

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon integer (ℤ.pos 1)))

<<<<<<< HEAD
_ : evalRaw test-case-03 ≡ expected-case-03
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `findFirstSetBit`.
pending-case-03 : Set
pending-case-03 = Pending (evalRaw test-case-03 ≡ expected-case-03)
>>>>>>> origin/master
```

## case-04

```
-- builtin/semantics/findFirstSetBit/case-04
test-case-04 : Untyped
<<<<<<< HEAD
test-case-04 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString "fff2"))))
=======
test-case-04 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString "\255\242"))))
>>>>>>> origin/master

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon integer (ℤ.pos 1)))

<<<<<<< HEAD
_ : evalRaw test-case-04 ≡ expected-case-04
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `findFirstSetBit`.
pending-case-04 : Set
pending-case-04 = Pending (evalRaw test-case-04 ≡ expected-case-04)
>>>>>>> origin/master
```

## case-05

```
-- builtin/semantics/findFirstSetBit/case-05
test-case-05 : Untyped
<<<<<<< HEAD
test-case-05 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))
=======
test-case-05 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))
>>>>>>> origin/master

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon integer (ℤ.negsuc 0)))

<<<<<<< HEAD
_ : evalRaw test-case-05 ≡ expected-case-05
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `findFirstSetBit`.
pending-case-05 : Set
pending-case-05 = Pending (evalRaw test-case-05 ≡ expected-case-05)
>>>>>>> origin/master
```

## case-06

```
-- builtin/semantics/findFirstSetBit/case-06
test-case-06 : Untyped
<<<<<<< HEAD
test-case-06 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString "00000000000000000000000000000000000000000000000000000000000000000000000000000000000001"))))
=======
test-case-06 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\SOH"))))
>>>>>>> origin/master

expected-case-06 : Result
expected-case-06 = success (UCon (tagCon integer (ℤ.pos 0)))

<<<<<<< HEAD
_ : evalRaw test-case-06 ≡ expected-case-06
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `findFirstSetBit`.
pending-case-06 : Set
pending-case-06 = Pending (evalRaw test-case-06 ≡ expected-case-06)
>>>>>>> origin/master
```

## case-07

```
-- builtin/semantics/findFirstSetBit/case-07
-- This returns 20, but should return 340
test-case-07 : Untyped
<<<<<<< HEAD
test-case-07 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString "50000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))
=======
test-case-07 = (UApp (UBuiltin findFirstSetBit) (UCon (tagCon bytestring (mkByteString "P\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))
>>>>>>> origin/master

expected-case-07 : Result
expected-case-07 = success (UCon (tagCon integer (ℤ.pos 340)))

<<<<<<< HEAD
_ : evalRaw test-case-07 ≡ expected-case-07
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `findFirstSetBit`.
pending-case-07 : Set
pending-case-07 = Pending (evalRaw test-case-07 ≡ expected-case-07)
>>>>>>> origin/master
```
