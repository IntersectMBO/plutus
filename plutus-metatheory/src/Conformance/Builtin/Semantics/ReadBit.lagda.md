---
title: Conformance.Builtin.Semantics.ReadBit
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/readBit`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ReadBit where

open import Conformance.Eval
```

## case-01

```
-- builtin/semantics/readBit/case-01
test-case-01 : Untyped
test-case-01 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.pos 0))))

expected-case-01 : Result
expected-case-01 = failure

_ : evalRaw test-case-01 ≡ expected-case-01
_ = refl
```

## case-02

```
-- builtin/semantics/readBit/case-02
test-case-02 : Untyped
test-case-02 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.pos 345))))

expected-case-02 : Result
expected-case-02 = failure

_ : evalRaw test-case-02 ≡ expected-case-02
_ = refl
```

## case-03

```
-- builtin/semantics/readBit/case-03
test-case-03 : Untyped
test-case-03 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.negsuc 0))))

expected-case-03 : Result
expected-case-03 = failure

_ : evalRaw test-case-03 ≡ expected-case-03
_ = refl
```

## case-04

```
-- builtin/semantics/readBit/case-04
test-case-04 : Untyped
test-case-04 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "ff")))) (UCon (tagCon integer (ℤ.negsuc 0))))

expected-case-04 : Result
expected-case-04 = failure

_ : evalRaw test-case-04 ≡ expected-case-04
_ = refl
```

## case-05

```
-- builtin/semantics/readBit/case-05
test-case-05 : Untyped
test-case-05 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 0))))

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon bool false))

_ : evalRaw test-case-05 ≡ expected-case-05
_ = refl
```

## case-06

```
-- builtin/semantics/readBit/case-06
test-case-06 : Untyped
test-case-06 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 1))))

expected-case-06 : Result
expected-case-06 = success (UCon (tagCon bool false))

_ : evalRaw test-case-06 ≡ expected-case-06
_ = refl
```

## case-07

```
-- builtin/semantics/readBit/case-07
test-case-07 : Untyped
test-case-07 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 2))))

expected-case-07 : Result
expected-case-07 = success (UCon (tagCon bool true))

_ : evalRaw test-case-07 ≡ expected-case-07
_ = refl
```

## case-08

```
-- builtin/semantics/readBit/case-08
test-case-08 : Untyped
test-case-08 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 3))))

expected-case-08 : Result
expected-case-08 = success (UCon (tagCon bool false))

_ : evalRaw test-case-08 ≡ expected-case-08
_ = refl
```

## case-09

```
-- builtin/semantics/readBit/case-09
test-case-09 : Untyped
test-case-09 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 4))))

expected-case-09 : Result
expected-case-09 = success (UCon (tagCon bool true))

_ : evalRaw test-case-09 ≡ expected-case-09
_ = refl
```

## case-10

```
-- builtin/semantics/readBit/case-10
test-case-10 : Untyped
test-case-10 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 5))))

expected-case-10 : Result
expected-case-10 = success (UCon (tagCon bool true))

_ : evalRaw test-case-10 ≡ expected-case-10
_ = refl
```

## case-11

```
-- builtin/semantics/readBit/case-11
test-case-11 : Untyped
test-case-11 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 6))))

expected-case-11 : Result
expected-case-11 = success (UCon (tagCon bool true))

_ : evalRaw test-case-11 ≡ expected-case-11
_ = refl
```

## case-12

```
-- builtin/semantics/readBit/case-12
test-case-12 : Untyped
test-case-12 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 7))))

expected-case-12 : Result
expected-case-12 = success (UCon (tagCon bool true))

_ : evalRaw test-case-12 ≡ expected-case-12
_ = refl
```

## case-13

```
-- builtin/semantics/readBit/case-13
test-case-13 : Untyped
test-case-13 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 8))))

expected-case-13 : Result
expected-case-13 = failure

_ : evalRaw test-case-13 ≡ expected-case-13
_ = refl
```

## case-14

```
-- builtin/semantics/readBit/case-14
test-case-14 : Untyped
test-case-14 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "fff4")))) (UCon (tagCon integer (ℤ.pos 16))))

expected-case-14 : Result
expected-case-14 = failure

_ : evalRaw test-case-14 ≡ expected-case-14
_ = refl
```

## case-15

```
-- builtin/semantics/readBit/case-15
test-case-15 : Untyped
test-case-15 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4ff")))) (UCon (tagCon integer (ℤ.pos 10))))

expected-case-15 : Result
expected-case-15 = success (UCon (tagCon bool true))

_ : evalRaw test-case-15 ≡ expected-case-15
_ = refl
```

## case-16

```
-- builtin/semantics/readBit/case-16
test-case-16 : Untyped
test-case-16 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 341))))

expected-case-16 : Result
expected-case-16 = success (UCon (tagCon bool true))

_ : evalRaw test-case-16 ≡ expected-case-16
_ = refl
```

## case-17

```
-- builtin/semantics/readBit/case-17
test-case-17 : Untyped
test-case-17 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 343))))

expected-case-17 : Result
expected-case-17 = success (UCon (tagCon bool false))

_ : evalRaw test-case-17 ≡ expected-case-17
_ = refl
```

## case-18

```
-- builtin/semantics/readBit/case-18
test-case-18 : Untyped
test-case-18 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 344))))

expected-case-18 : Result
expected-case-18 = failure

_ : evalRaw test-case-18 ≡ expected-case-18
_ = refl
```

## case-19

```
-- builtin/semantics/readBit/case-19
test-case-19 : Untyped
test-case-19 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 9223372036854775807))))

expected-case-19 : Result
expected-case-19 = failure

_ : evalRaw test-case-19 ≡ expected-case-19
_ = refl
```

## case-20

```
-- builtin/semantics/readBit/case-20
test-case-20 : Untyped
test-case-20 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 9223372036854775808))))

expected-case-20 : Result
expected-case-20 = failure

_ : evalRaw test-case-20 ≡ expected-case-20
_ = refl
```

## case-21

```
-- builtin/semantics/readBit/case-21
test-case-21 : Untyped
test-case-21 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.negsuc 9223372036854775807))))

expected-case-21 : Result
expected-case-21 = failure

_ : evalRaw test-case-21 ≡ expected-case-21
_ = refl
```

## case-22

```
-- builtin/semantics/readBit/case-22
test-case-22 : Untyped
test-case-22 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.negsuc 9223372036854775808))))

expected-case-22 : Result
expected-case-22 = failure

_ : evalRaw test-case-22 ≡ expected-case-22
_ = refl
```
