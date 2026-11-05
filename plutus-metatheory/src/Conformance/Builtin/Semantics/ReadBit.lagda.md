---
title: Conformance.Builtin.Semantics.ReadBit
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

<<<<<<< HEAD
_ : evalRaw test-case-01 ≡ expected-case-01
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-01 : Set
pending-case-01 = Pending (evalRaw test-case-01 ≡ expected-case-01)
>>>>>>> origin/master
```

## case-02

```
-- builtin/semantics/readBit/case-02
test-case-02 : Untyped
test-case-02 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.pos 345))))

expected-case-02 : Result
expected-case-02 = failure

<<<<<<< HEAD
_ : evalRaw test-case-02 ≡ expected-case-02
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-02 : Set
pending-case-02 = Pending (evalRaw test-case-02 ≡ expected-case-02)
>>>>>>> origin/master
```

## case-03

```
-- builtin/semantics/readBit/case-03
test-case-03 : Untyped
test-case-03 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.negsuc 0))))

expected-case-03 : Result
expected-case-03 = failure

<<<<<<< HEAD
_ : evalRaw test-case-03 ≡ expected-case-03
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-03 : Set
pending-case-03 = Pending (evalRaw test-case-03 ≡ expected-case-03)
>>>>>>> origin/master
```

## case-04

```
-- builtin/semantics/readBit/case-04
test-case-04 : Untyped
<<<<<<< HEAD
test-case-04 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "ff")))) (UCon (tagCon integer (ℤ.negsuc 0))))
=======
test-case-04 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon integer (ℤ.negsuc 0))))
>>>>>>> origin/master

expected-case-04 : Result
expected-case-04 = failure

<<<<<<< HEAD
_ : evalRaw test-case-04 ≡ expected-case-04
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-04 : Set
pending-case-04 = Pending (evalRaw test-case-04 ≡ expected-case-04)
>>>>>>> origin/master
```

## case-05

```
-- builtin/semantics/readBit/case-05
test-case-05 : Untyped
<<<<<<< HEAD
test-case-05 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 0))))
=======
test-case-05 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 0))))
>>>>>>> origin/master

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon bool false))

<<<<<<< HEAD
_ : evalRaw test-case-05 ≡ expected-case-05
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-05 : Set
pending-case-05 = Pending (evalRaw test-case-05 ≡ expected-case-05)
>>>>>>> origin/master
```

## case-06

```
-- builtin/semantics/readBit/case-06
test-case-06 : Untyped
<<<<<<< HEAD
test-case-06 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 1))))
=======
test-case-06 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 1))))
>>>>>>> origin/master

expected-case-06 : Result
expected-case-06 = success (UCon (tagCon bool false))

<<<<<<< HEAD
_ : evalRaw test-case-06 ≡ expected-case-06
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-06 : Set
pending-case-06 = Pending (evalRaw test-case-06 ≡ expected-case-06)
>>>>>>> origin/master
```

## case-07

```
-- builtin/semantics/readBit/case-07
test-case-07 : Untyped
<<<<<<< HEAD
test-case-07 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 2))))
=======
test-case-07 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 2))))
>>>>>>> origin/master

expected-case-07 : Result
expected-case-07 = success (UCon (tagCon bool true))

<<<<<<< HEAD
_ : evalRaw test-case-07 ≡ expected-case-07
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-07 : Set
pending-case-07 = Pending (evalRaw test-case-07 ≡ expected-case-07)
>>>>>>> origin/master
```

## case-08

```
-- builtin/semantics/readBit/case-08
test-case-08 : Untyped
<<<<<<< HEAD
test-case-08 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 3))))
=======
test-case-08 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 3))))
>>>>>>> origin/master

expected-case-08 : Result
expected-case-08 = success (UCon (tagCon bool false))

<<<<<<< HEAD
_ : evalRaw test-case-08 ≡ expected-case-08
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-08 : Set
pending-case-08 = Pending (evalRaw test-case-08 ≡ expected-case-08)
>>>>>>> origin/master
```

## case-09

```
-- builtin/semantics/readBit/case-09
test-case-09 : Untyped
<<<<<<< HEAD
test-case-09 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 4))))
=======
test-case-09 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 4))))
>>>>>>> origin/master

expected-case-09 : Result
expected-case-09 = success (UCon (tagCon bool true))

<<<<<<< HEAD
_ : evalRaw test-case-09 ≡ expected-case-09
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-09 : Set
pending-case-09 = Pending (evalRaw test-case-09 ≡ expected-case-09)
>>>>>>> origin/master
```

## case-10

```
-- builtin/semantics/readBit/case-10
test-case-10 : Untyped
<<<<<<< HEAD
test-case-10 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 5))))
=======
test-case-10 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 5))))
>>>>>>> origin/master

expected-case-10 : Result
expected-case-10 = success (UCon (tagCon bool true))

<<<<<<< HEAD
_ : evalRaw test-case-10 ≡ expected-case-10
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-10 : Set
pending-case-10 = Pending (evalRaw test-case-10 ≡ expected-case-10)
>>>>>>> origin/master
```

## case-11

```
-- builtin/semantics/readBit/case-11
test-case-11 : Untyped
<<<<<<< HEAD
test-case-11 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 6))))
=======
test-case-11 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 6))))
>>>>>>> origin/master

expected-case-11 : Result
expected-case-11 = success (UCon (tagCon bool true))

<<<<<<< HEAD
_ : evalRaw test-case-11 ≡ expected-case-11
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-11 : Set
pending-case-11 = Pending (evalRaw test-case-11 ≡ expected-case-11)
>>>>>>> origin/master
```

## case-12

```
-- builtin/semantics/readBit/case-12
test-case-12 : Untyped
<<<<<<< HEAD
test-case-12 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 7))))
=======
test-case-12 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 7))))
>>>>>>> origin/master

expected-case-12 : Result
expected-case-12 = success (UCon (tagCon bool true))

<<<<<<< HEAD
_ : evalRaw test-case-12 ≡ expected-case-12
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-12 : Set
pending-case-12 = Pending (evalRaw test-case-12 ≡ expected-case-12)
>>>>>>> origin/master
```

## case-13

```
-- builtin/semantics/readBit/case-13
test-case-13 : Untyped
<<<<<<< HEAD
test-case-13 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4")))) (UCon (tagCon integer (ℤ.pos 8))))
=======
test-case-13 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 8))))
>>>>>>> origin/master

expected-case-13 : Result
expected-case-13 = failure

<<<<<<< HEAD
_ : evalRaw test-case-13 ≡ expected-case-13
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-13 : Set
pending-case-13 = Pending (evalRaw test-case-13 ≡ expected-case-13)
>>>>>>> origin/master
```

## case-14

```
-- builtin/semantics/readBit/case-14
test-case-14 : Untyped
<<<<<<< HEAD
test-case-14 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "fff4")))) (UCon (tagCon integer (ℤ.pos 16))))
=======
test-case-14 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\255\244")))) (UCon (tagCon integer (ℤ.pos 16))))
>>>>>>> origin/master

expected-case-14 : Result
expected-case-14 = failure

<<<<<<< HEAD
_ : evalRaw test-case-14 ≡ expected-case-14
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-14 : Set
pending-case-14 = Pending (evalRaw test-case-14 ≡ expected-case-14)
>>>>>>> origin/master
```

## case-15

```
-- builtin/semantics/readBit/case-15
test-case-15 : Untyped
<<<<<<< HEAD
test-case-15 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "f4ff")))) (UCon (tagCon integer (ℤ.pos 10))))
=======
test-case-15 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244\255")))) (UCon (tagCon integer (ℤ.pos 10))))
>>>>>>> origin/master

expected-case-15 : Result
expected-case-15 = success (UCon (tagCon bool true))

<<<<<<< HEAD
_ : evalRaw test-case-15 ≡ expected-case-15
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-15 : Set
pending-case-15 = Pending (evalRaw test-case-15 ≡ expected-case-15)
>>>>>>> origin/master
```

## case-16

```
-- builtin/semantics/readBit/case-16
test-case-16 : Untyped
<<<<<<< HEAD
test-case-16 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 341))))
=======
test-case-16 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 341))))
>>>>>>> origin/master

expected-case-16 : Result
expected-case-16 = success (UCon (tagCon bool true))

<<<<<<< HEAD
_ : evalRaw test-case-16 ≡ expected-case-16
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-16 : Set
pending-case-16 = Pending (evalRaw test-case-16 ≡ expected-case-16)
>>>>>>> origin/master
```

## case-17

```
-- builtin/semantics/readBit/case-17
test-case-17 : Untyped
<<<<<<< HEAD
test-case-17 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 343))))
=======
test-case-17 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 343))))
>>>>>>> origin/master

expected-case-17 : Result
expected-case-17 = success (UCon (tagCon bool false))

<<<<<<< HEAD
_ : evalRaw test-case-17 ≡ expected-case-17
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-17 : Set
pending-case-17 = Pending (evalRaw test-case-17 ≡ expected-case-17)
>>>>>>> origin/master
```

## case-18

```
-- builtin/semantics/readBit/case-18
test-case-18 : Untyped
<<<<<<< HEAD
test-case-18 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 344))))
=======
test-case-18 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 344))))
>>>>>>> origin/master

expected-case-18 : Result
expected-case-18 = failure

<<<<<<< HEAD
_ : evalRaw test-case-18 ≡ expected-case-18
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-18 : Set
pending-case-18 = Pending (evalRaw test-case-18 ≡ expected-case-18)
>>>>>>> origin/master
```

## case-19

```
-- builtin/semantics/readBit/case-19
test-case-19 : Untyped
<<<<<<< HEAD
test-case-19 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 9223372036854775807))))
=======
test-case-19 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 9223372036854775807))))
>>>>>>> origin/master

expected-case-19 : Result
expected-case-19 = failure

<<<<<<< HEAD
_ : evalRaw test-case-19 ≡ expected-case-19
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-19 : Set
pending-case-19 = Pending (evalRaw test-case-19 ≡ expected-case-19)
>>>>>>> origin/master
```

## case-20

```
-- builtin/semantics/readBit/case-20
test-case-20 : Untyped
<<<<<<< HEAD
test-case-20 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.pos 9223372036854775808))))
=======
test-case-20 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 9223372036854775808))))
>>>>>>> origin/master

expected-case-20 : Result
expected-case-20 = failure

<<<<<<< HEAD
_ : evalRaw test-case-20 ≡ expected-case-20
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-20 : Set
pending-case-20 = Pending (evalRaw test-case-20 ≡ expected-case-20)
>>>>>>> origin/master
```

## case-21

```
-- builtin/semantics/readBit/case-21
test-case-21 : Untyped
<<<<<<< HEAD
test-case-21 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.negsuc 9223372036854775807))))
=======
test-case-21 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.negsuc 9223372036854775807))))
>>>>>>> origin/master

expected-case-21 : Result
expected-case-21 = failure

<<<<<<< HEAD
_ : evalRaw test-case-21 ≡ expected-case-21
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-21 : Set
pending-case-21 = Pending (evalRaw test-case-21 ≡ expected-case-21)
>>>>>>> origin/master
```

## case-22

```
-- builtin/semantics/readBit/case-22
test-case-22 : Untyped
<<<<<<< HEAD
test-case-22 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon integer (ℤ.negsuc 9223372036854775808))))
=======
test-case-22 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.negsuc 9223372036854775808))))
>>>>>>> origin/master

expected-case-22 : Result
expected-case-22 = failure

<<<<<<< HEAD
_ : evalRaw test-case-22 ≡ expected-case-22
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-22 : Set
pending-case-22 = Pending (evalRaw test-case-22 ≡ expected-case-22)
>>>>>>> origin/master
```
