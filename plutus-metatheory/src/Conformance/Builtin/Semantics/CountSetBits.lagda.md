---
title: Conformance.Builtin.Semantics.CountSetBits
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/countSetBits`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.CountSetBits where

open import Conformance.Eval
```

## case-01

```
-- builtin/semantics/countSetBits/case-01
test-case-01 : Untyped
test-case-01 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString ""))))

expected-case-01 : Result
expected-case-01 = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-case-01 ≡ expected-case-01
_ = refl
```

## case-02

```
-- builtin/semantics/countSetBits/case-02
test-case-02 : Untyped
test-case-02 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "0000"))))

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-case-02 ≡ expected-case-02
_ = refl
```

## case-03

```
-- builtin/semantics/countSetBits/case-03
test-case-03 : Untyped
test-case-03 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "0100"))))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-case-03 ≡ expected-case-03
_ = refl
```

## case-04

```
-- builtin/semantics/countSetBits/case-04
test-case-04 : Untyped
test-case-04 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "0001"))))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-case-04 ≡ expected-case-04
_ = refl
```

## case-05

```
-- builtin/semantics/countSetBits/case-05
test-case-05 : Untyped
test-case-05 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0"))))

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon integer (ℤ.pos 163)))

_ : evalRaw test-case-05 ≡ expected-case-05
_ = refl
```

## case-06

```
-- builtin/semantics/countSetBits/case-06
test-case-06 : Untyped
test-case-06 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000"))))

expected-case-06 : Result
expected-case-06 = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-case-06 ≡ expected-case-06
_ = refl
```

## case-07

```
-- builtin/semantics/countSetBits/case-07
test-case-07 : Untyped
test-case-07 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "00000000000000100000000000000000000000000000000000000000000000000000000000000000000000"))))

expected-case-07 : Result
expected-case-07 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-case-07 ≡ expected-case-07
_ = refl
```

## case-08

```
-- builtin/semantics/countSetBits/case-08
test-case-08 : Untyped
test-case-08 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"))))

expected-case-08 : Result
expected-case-08 = success (UCon (tagCon integer (ℤ.pos 344)))

_ : evalRaw test-case-08 ≡ expected-case-08
_ = refl
```
