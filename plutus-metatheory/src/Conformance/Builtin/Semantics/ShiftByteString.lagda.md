---
title: Conformance.Builtin.Semantics.ShiftByteString
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/shiftByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ShiftByteString where

open import Conformance.Eval
```

## case-01

```
-- builtin/semantics/shiftByteString/case-01
test-case-01 : Untyped
test-case-01 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.pos 3))))

expected-case-01 : Result
expected-case-01 = success (UCon (tagCon bytestring (mkByteString "")))

_ : evalRaw test-case-01 ≡ expected-case-01
_ = refl
```

## case-02

```
-- builtin/semantics/shiftByteString/case-02
test-case-02 : Untyped
test-case-02 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.negsuc 2))))

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon bytestring (mkByteString "")))

_ : evalRaw test-case-02 ≡ expected-case-02
_ = refl
```

## case-03

```
-- builtin/semantics/shiftByteString/case-03
test-case-03 : Untyped
test-case-03 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "ebfc")))) (UCon (tagCon integer (ℤ.pos 5))))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon bytestring (mkByteString "7f80")))

_ : evalRaw test-case-03 ≡ expected-case-03
_ = refl
```

## case-04

```
-- builtin/semantics/shiftByteString/case-04
test-case-04 : Untyped
test-case-04 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "ebfc")))) (UCon (tagCon integer (ℤ.negsuc 4))))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon bytestring (mkByteString "075f")))

_ : evalRaw test-case-04 ≡ expected-case-04
_ = refl
```

## case-05

```
-- builtin/semantics/shiftByteString/case-05
test-case-05 : Untyped
test-case-05 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "ebfc")))) (UCon (tagCon integer (ℤ.pos 16))))

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon bytestring (mkByteString "0000")))

_ : evalRaw test-case-05 ≡ expected-case-05
_ = refl
```

## case-06

```
-- builtin/semantics/shiftByteString/case-06
test-case-06 : Untyped
test-case-06 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "ebfc")))) (UCon (tagCon integer (ℤ.negsuc 15))))

expected-case-06 : Result
expected-case-06 = success (UCon (tagCon bytestring (mkByteString "0000")))

_ : evalRaw test-case-06 ≡ expected-case-06
_ = refl
```

## case-07

```
-- builtin/semantics/shiftByteString/case-07
-- Shift by 0: the result should be the same as the input.
test-case-07 : Untyped
test-case-07 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 0))))

expected-case-07 : Result
expected-case-07 = success (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))

_ : evalRaw test-case-07 ≡ expected-case-07
_ = refl
```

## case-08

```
-- builtin/semantics/shiftByteString/case-08
test-case-08 : Untyped
test-case-08 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 23))))

expected-case-08 : Result
expected-case-08 = success (UCon (tagCon bytestring (mkByteString "6b42c2401dcee02d9d85ce5eb341f6e0673a15d84cabb09f220a8102b3ce9fb0d233d92e63ac51d8000000")))

_ : evalRaw test-case-08 ≡ expected-case-08
_ = refl
```

## case-09

```
-- builtin/semantics/shiftByteString/case-09
test-case-09 : Untyped
test-case-09 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.negsuc 22))))

expected-case-09 : Result
expected-case-09 = success (UCon (tagCon bytestring (mkByteString "0000006785e1ad0b0900773b80b67617397acd07db819ce8576132aec27c882a040acf3a7ec348cf64b98e")))

_ : evalRaw test-case-09 ≡ expected-case-09
_ = refl
```

## case-10

```
-- builtin/semantics/shiftByteString/case-10
test-case-10 : Untyped
test-case-10 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 1000000))))

expected-case-10 : Result
expected-case-10 = success (UCon (tagCon bytestring (mkByteString "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))

_ : evalRaw test-case-10 ≡ expected-case-10
_ = refl
```

## case-11

```
-- builtin/semantics/shiftByteString/case-11
test-case-11 : Untyped
test-case-11 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.negsuc 999999))))

expected-case-11 : Result
expected-case-11 = success (UCon (tagCon bytestring (mkByteString "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))

_ : evalRaw test-case-11 ≡ expected-case-11
_ = refl
```

## case-12

```
-- builtin/semantics/shiftByteString/case-12
-- Shift by maxBound :: Int64
test-case-12 : Untyped
test-case-12 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 9223372036854775807))))

expected-case-12 : Result
expected-case-12 = success (UCon (tagCon bytestring (mkByteString "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))

_ : evalRaw test-case-12 ≡ expected-case-12
_ = refl
```

## case-13

```
-- builtin/semantics/shiftByteString/case-13
-- Shift by (maxBound :: Int64) + 1
test-case-13 : Untyped
test-case-13 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 9223372036854775808))))

expected-case-13 : Result
expected-case-13 = failure

_ : evalRaw test-case-13 ≡ expected-case-13
_ = refl
```

## case-14

```
-- builtin/semantics/shiftByteString/case-14
-- Shift by minBound :: Int64
test-case-14 : Untyped
test-case-14 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.negsuc 9223372036854775807))))

expected-case-14 : Result
expected-case-14 = success (UCon (tagCon bytestring (mkByteString "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000")))

_ : evalRaw test-case-14 ≡ expected-case-14
_ = refl
```

## case-15

```
-- builtin/semantics/shiftByteString/case-15
-- Shift by (minBound :: Int64) - 1
test-case-15 : Untyped
test-case-15 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.negsuc 9223372036854775808))))

expected-case-15 : Result
expected-case-15 = failure

_ : evalRaw test-case-15 ≡ expected-case-15
_ = refl
```
