---
title: Conformance.Builtin.Semantics.XorByteString
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/xorByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.XorByteString where

open import Conformance.Eval
```

## case-01

```
-- builtin/semantics/xorByteString/case-01
test-case-01 : Untyped
test-case-01 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "ff"))))

expected-case-01 : Result
expected-case-01 = success (UCon (tagCon bytestring (mkByteString "")))

_ : evalRaw test-case-01 ≡ expected-case-01
_ = refl
```

## case-02

```
-- builtin/semantics/xorByteString/case-02
test-case-02 : Untyped
test-case-02 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "ff")))) (UCon (tagCon bytestring (mkByteString ""))))

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon bytestring (mkByteString "")))

_ : evalRaw test-case-02 ≡ expected-case-02
_ = refl
```

## case-03

```
-- builtin/semantics/xorByteString/case-03
test-case-03 : Untyped
test-case-03 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "ff")))) (UCon (tagCon bytestring (mkByteString "00"))))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon bytestring (mkByteString "ff")))

_ : evalRaw test-case-03 ≡ expected-case-03
_ = refl
```

## case-04

```
-- builtin/semantics/xorByteString/case-04
test-case-04 : Untyped
test-case-04 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "00")))) (UCon (tagCon bytestring (mkByteString "ff"))))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon bytestring (mkByteString "ff")))

_ : evalRaw test-case-04 ≡ expected-case-04
_ = refl
```

## case-05

```
-- builtin/semantics/xorByteString/case-05
test-case-05 : Untyped
test-case-05 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "4f00")))) (UCon (tagCon bytestring (mkByteString "f4"))))

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon bytestring (mkByteString "bb")))

_ : evalRaw test-case-05 ≡ expected-case-05
_ = refl
```

## case-06

```
-- builtin/semantics/xorByteString/case-06
test-case-06 : Untyped
test-case-06 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "ff"))))

expected-case-06 : Result
expected-case-06 = success (UCon (tagCon bytestring (mkByteString "ff")))

_ : evalRaw test-case-06 ≡ expected-case-06
_ = refl
```

## case-07

```
-- builtin/semantics/xorByteString/case-07
test-case-07 : Untyped
test-case-07 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "ff")))) (UCon (tagCon bytestring (mkByteString ""))))

expected-case-07 : Result
expected-case-07 = success (UCon (tagCon bytestring (mkByteString "ff")))

_ : evalRaw test-case-07 ≡ expected-case-07
_ = refl
```

## case-08

```
-- builtin/semantics/xorByteString/case-08
test-case-08 : Untyped
test-case-08 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "ff")))) (UCon (tagCon bytestring (mkByteString "00"))))

expected-case-08 : Result
expected-case-08 = success (UCon (tagCon bytestring (mkByteString "ff")))

_ : evalRaw test-case-08 ≡ expected-case-08
_ = refl
```

## case-09

```
-- builtin/semantics/xorByteString/case-09
test-case-09 : Untyped
test-case-09 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "00")))) (UCon (tagCon bytestring (mkByteString "ff"))))

expected-case-09 : Result
expected-case-09 = success (UCon (tagCon bytestring (mkByteString "ff")))

_ : evalRaw test-case-09 ≡ expected-case-09
_ = refl
```

## case-10

```
-- builtin/semantics/xorByteString/case-10
test-case-10 : Untyped
test-case-10 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "4f00")))) (UCon (tagCon bytestring (mkByteString "f4"))))

expected-case-10 : Result
expected-case-10 = success (UCon (tagCon bytestring (mkByteString "bb00")))

_ : evalRaw test-case-10 ≡ expected-case-10
_ = refl
```

## case-11

```
-- builtin/semantics/xorByteString/case-11
test-case-11 : Untyped
test-case-11 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon bytestring (mkByteString "db9c861c98a3d19cb928c22a32aaae0a4f740113dc48734d3c001657cb8fd2b9497faf16a40c1ecdd7d6581b55b625553af3"))))

expected-case-11 : Result
expected-case-11 = success (UCon (tagCon bytestring (mkByteString "e85e76ca1d2751a724e899113936136ccc99c1dda863c3d46b612813de8dd7ded440ceb2c3be420a8f75e8")))

_ : evalRaw test-case-11 ≡ expected-case-11
_ = refl
```

## case-12

```
-- builtin/semantics/xorByteString/case-12
test-case-12 : Untyped
test-case-12 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon bytestring (mkByteString "db9c861c98a3d19cb928c22a32aaae0a4f740113dc48734d3c001657cb8fd2b9497faf16a40c1ecdd7d6581b55b625553af3"))))

expected-case-12 : Result
expected-case-12 = success (UCon (tagCon bytestring (mkByteString "e85e76ca1d2751a724e899113936136ccc99c1dda863c3d46b612813de8dd7ded440ceb2c3be420a8f75e81b55b625553af3")))

_ : evalRaw test-case-12 ≡ expected-case-12
_ = refl
```

## case-13

```
-- builtin/semantics/xorByteString/case-13
test-case-13 : Untyped
test-case-13 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "db9c861c98a3d19cb928c22a32aaae0a4f740113dc48734d3c001657cb8fd2b9497faf16a40c1ecdd7d6581b55b625553af3")))) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0"))))

expected-case-13 : Result
expected-case-13 = success (UCon (tagCon bytestring (mkByteString "e85e76ca1d2751a724e899113936136ccc99c1dda863c3d46b612813de8dd7ded440ceb2c3be420a8f75e8")))

_ : evalRaw test-case-13 ≡ expected-case-13
_ = refl
```

## case-14

```
-- builtin/semantics/xorByteString/case-14
test-case-14 : Untyped
test-case-14 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "db9c861c98a3d19cb928c22a32aaae0a4f740113dc48734d3c001657cb8fd2b9497faf16a40c1ecdd7d6581b55b625553af3")))) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0"))))

expected-case-14 : Result
expected-case-14 = success (UCon (tagCon bytestring (mkByteString "e85e76ca1d2751a724e899113936136ccc99c1dda863c3d46b612813de8dd7ded440ceb2c3be420a8f75e81b55b625553af3")))

_ : evalRaw test-case-14 ≡ expected-case-14
_ = refl
```
