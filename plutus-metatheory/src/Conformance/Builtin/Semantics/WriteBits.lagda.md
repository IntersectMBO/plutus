---
title: Conformance.Builtin.Semantics.WriteBits
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/writeBits`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.WriteBits where

open import Conformance.Eval
```

## case-01

```
-- builtin/semantics/writeBits/case-01
test-case-01 : Untyped
test-case-01 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ [])))) (UCon (tagCon bool false)))

expected-case-01 : Result
expected-case-01 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-01 : Set
pending-case-01 = Pending (evalRaw test-case-01 ≡ expected-case-01)
```

## case-02

```
-- builtin/semantics/writeBits/case-02
test-case-02 : Untyped
test-case-02 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon (list integer) ((ℤ.pos 15) ∷ [])))) (UCon (tagCon bool false)))

expected-case-02 : Result
expected-case-02 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-02 : Set
pending-case-02 = Pending (evalRaw test-case-02 ≡ expected-case-02)
```

## case-03

```
-- builtin/semantics/writeBits/case-03
test-case-03 : Untyped
test-case-03 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ [])))) (UCon (tagCon bool true)))

expected-case-03 : Result
expected-case-03 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-03 : Set
pending-case-03 = Pending (evalRaw test-case-03 ≡ expected-case-03)
```

## case-04

```
-- builtin/semantics/writeBits/case-04
test-case-04 : Untyped
test-case-04 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ (ℤ.pos 1) ∷ [])))) (UCon (tagCon bool false)))

expected-case-04 : Result
expected-case-04 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-04 : Set
pending-case-04 = Pending (evalRaw test-case-04 ≡ expected-case-04)
```

## case-05

```
-- builtin/semantics/writeBits/case-05
test-case-05 : Untyped
test-case-05 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.negsuc 0) ∷ [])))) (UCon (tagCon bool false)))

expected-case-05 : Result
expected-case-05 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-05 : Set
pending-case-05 = Pending (evalRaw test-case-05 ≡ expected-case-05)
```

## case-06

```
-- builtin/semantics/writeBits/case-06
test-case-06 : Untyped
test-case-06 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ (ℤ.negsuc 0) ∷ [])))) (UCon (tagCon bool false)))

expected-case-06 : Result
expected-case-06 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-06 : Set
pending-case-06 = Pending (evalRaw test-case-06 ≡ expected-case-06)
```

## case-07

```
-- builtin/semantics/writeBits/case-07
test-case-07 : Untyped
test-case-07 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.negsuc 0) ∷ (ℤ.pos 0) ∷ [])))) (UCon (tagCon bool false)))

expected-case-07 : Result
expected-case-07 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-07 : Set
pending-case-07 = Pending (evalRaw test-case-07 ≡ expected-case-07)
```

## case-08

```
-- builtin/semantics/writeBits/case-08
test-case-08 : Untyped
test-case-08 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 8) ∷ [])))) (UCon (tagCon bool false)))

expected-case-08 : Result
expected-case-08 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-08 : Set
pending-case-08 = Pending (evalRaw test-case-08 ≡ expected-case-08)
```

## case-09

```
-- builtin/semantics/writeBits/case-09
test-case-09 : Untyped
test-case-09 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 8) ∷ [])))) (UCon (tagCon bool false)))

expected-case-09 : Result
expected-case-09 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-09 : Set
pending-case-09 = Pending (evalRaw test-case-09 ≡ expected-case-09)
```

## case-10

```
-- builtin/semantics/writeBits/case-10
test-case-10 : Untyped
test-case-10 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 8) ∷ (ℤ.pos 1) ∷ [])))) (UCon (tagCon bool false)))

expected-case-10 : Result
expected-case-10 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-10 : Set
pending-case-10 = Pending (evalRaw test-case-10 ≡ expected-case-10)
```

## case-11

```
-- builtin/semantics/writeBits/case-11
test-case-11 : Untyped
test-case-11 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ [])))) (UCon (tagCon bool false)))

expected-case-11 : Result
expected-case-11 = success (UCon (tagCon bytestring (mkByteString "\254")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-11 : Set
pending-case-11 = Pending (evalRaw test-case-11 ≡ expected-case-11)
```

## case-12

```
-- builtin/semantics/writeBits/case-12
test-case-12 : Untyped
test-case-12 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ [])))) (UCon (tagCon bool false)))

expected-case-12 : Result
expected-case-12 = success (UCon (tagCon bytestring (mkByteString "\253")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-12 : Set
pending-case-12 = Pending (evalRaw test-case-12 ≡ expected-case-12)
```

## case-13

```
-- builtin/semantics/writeBits/case-13
test-case-13 : Untyped
test-case-13 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 2) ∷ [])))) (UCon (tagCon bool false)))

expected-case-13 : Result
expected-case-13 = success (UCon (tagCon bytestring (mkByteString "\251")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-13 : Set
pending-case-13 = Pending (evalRaw test-case-13 ≡ expected-case-13)
```

## case-14

```
-- builtin/semantics/writeBits/case-14
test-case-14 : Untyped
test-case-14 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 3) ∷ [])))) (UCon (tagCon bool false)))

expected-case-14 : Result
expected-case-14 = success (UCon (tagCon bytestring (mkByteString "\247")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-14 : Set
pending-case-14 = Pending (evalRaw test-case-14 ≡ expected-case-14)
```

## case-15

```
-- builtin/semantics/writeBits/case-15
test-case-15 : Untyped
test-case-15 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 4) ∷ [])))) (UCon (tagCon bool false)))

expected-case-15 : Result
expected-case-15 = success (UCon (tagCon bytestring (mkByteString "\239")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-15 : Set
pending-case-15 = Pending (evalRaw test-case-15 ≡ expected-case-15)
```

## case-16

```
-- builtin/semantics/writeBits/case-16
test-case-16 : Untyped
test-case-16 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 5) ∷ [])))) (UCon (tagCon bool false)))

expected-case-16 : Result
expected-case-16 = success (UCon (tagCon bytestring (mkByteString "\223")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-16 : Set
pending-case-16 = Pending (evalRaw test-case-16 ≡ expected-case-16)
```

## case-17

```
-- builtin/semantics/writeBits/case-17
test-case-17 : Untyped
test-case-17 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 6) ∷ [])))) (UCon (tagCon bool false)))

expected-case-17 : Result
expected-case-17 = success (UCon (tagCon bytestring (mkByteString "\191")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-17 : Set
pending-case-17 = Pending (evalRaw test-case-17 ≡ expected-case-17)
```

## case-18

```
-- builtin/semantics/writeBits/case-18
test-case-18 : Untyped
test-case-18 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 7) ∷ [])))) (UCon (tagCon bool false)))

expected-case-18 : Result
expected-case-18 = success (UCon (tagCon bytestring (mkByteString "\DEL")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-18 : Set
pending-case-18 = Pending (evalRaw test-case-18 ≡ expected-case-18)
```

## case-19

```
-- builtin/semantics/writeBits/case-19
test-case-19 : Untyped
test-case-19 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon (list integer) ((ℤ.negsuc 0) ∷ [])))) (UCon (tagCon bool true)))

expected-case-19 : Result
expected-case-19 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-19 : Set
pending-case-19 = Pending (evalRaw test-case-19 ≡ expected-case-19)
```

## case-20

```
-- builtin/semantics/writeBits/case-20
test-case-20 : Untyped
test-case-20 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ [])))) (UCon (tagCon bool true)))

expected-case-20 : Result
expected-case-20 = success (UCon (tagCon bytestring (mkByteString "\SOH")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-20 : Set
pending-case-20 = Pending (evalRaw test-case-20 ≡ expected-case-20)
```

## case-21

```
-- builtin/semantics/writeBits/case-21
test-case-21 : Untyped
test-case-21 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ [])))) (UCon (tagCon bool true)))

expected-case-21 : Result
expected-case-21 = success (UCon (tagCon bytestring (mkByteString "\STX")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-21 : Set
pending-case-21 = Pending (evalRaw test-case-21 ≡ expected-case-21)
```

## case-22

```
-- builtin/semantics/writeBits/case-22
test-case-22 : Untyped
test-case-22 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 2) ∷ [])))) (UCon (tagCon bool true)))

expected-case-22 : Result
expected-case-22 = success (UCon (tagCon bytestring (mkByteString "\EOT")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-22 : Set
pending-case-22 = Pending (evalRaw test-case-22 ≡ expected-case-22)
```

## case-23

```
-- builtin/semantics/writeBits/case-23
test-case-23 : Untyped
test-case-23 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 3) ∷ [])))) (UCon (tagCon bool true)))

expected-case-23 : Result
expected-case-23 = success (UCon (tagCon bytestring (mkByteString "\b")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-23 : Set
pending-case-23 = Pending (evalRaw test-case-23 ≡ expected-case-23)
```

## case-24

```
-- builtin/semantics/writeBits/case-24
test-case-24 : Untyped
test-case-24 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 4) ∷ [])))) (UCon (tagCon bool true)))

expected-case-24 : Result
expected-case-24 = success (UCon (tagCon bytestring (mkByteString "\DLE")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-24 : Set
pending-case-24 = Pending (evalRaw test-case-24 ≡ expected-case-24)
```

## case-25

```
-- builtin/semantics/writeBits/case-25
test-case-25 : Untyped
test-case-25 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 5) ∷ [])))) (UCon (tagCon bool true)))

expected-case-25 : Result
expected-case-25 = success (UCon (tagCon bytestring (mkByteString " ")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-25 : Set
pending-case-25 = Pending (evalRaw test-case-25 ≡ expected-case-25)
```

## case-26

```
-- builtin/semantics/writeBits/case-26
test-case-26 : Untyped
test-case-26 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 6) ∷ [])))) (UCon (tagCon bool true)))

expected-case-26 : Result
expected-case-26 = success (UCon (tagCon bytestring (mkByteString "@")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-26 : Set
pending-case-26 = Pending (evalRaw test-case-26 ≡ expected-case-26)
```

## case-27

```
-- builtin/semantics/writeBits/case-27
test-case-27 : Untyped
test-case-27 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 7) ∷ [])))) (UCon (tagCon bool true)))

expected-case-27 : Result
expected-case-27 = success (UCon (tagCon bytestring (mkByteString "\128")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-27 : Set
pending-case-27 = Pending (evalRaw test-case-27 ≡ expected-case-27)
```

## case-28

```
-- builtin/semantics/writeBits/case-28
test-case-28 : Untyped
test-case-28 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 8) ∷ [])))) (UCon (tagCon bool true)))

expected-case-28 : Result
expected-case-28 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-28 : Set
pending-case-28 = Pending (evalRaw test-case-28 ≡ expected-case-28)
```

## case-29

```
-- builtin/semantics/writeBits/case-29
test-case-29 : Untyped
test-case-29 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\244\255")))) (UCon (tagCon (list integer) ((ℤ.pos 10) ∷ [])))) (UCon (tagCon bool false)))

expected-case-29 : Result
expected-case-29 = success (UCon (tagCon bytestring (mkByteString "\240\255")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-29 : Set
pending-case-29 = Pending (evalRaw test-case-29 ≡ expected-case-29)
```

## case-30

```
-- builtin/semantics/writeBits/case-30
test-case-30 : Untyped
test-case-30 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\244\255")))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 10) ∷ [])))) (UCon (tagCon bool false)))

expected-case-30 : Result
expected-case-30 = success (UCon (tagCon bytestring (mkByteString "\240\253")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-30 : Set
pending-case-30 = Pending (evalRaw test-case-30 ≡ expected-case-30)
```

## case-31

```
-- builtin/semantics/writeBits/case-31
test-case-31 : Untyped
test-case-31 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\244\255")))) (UCon (tagCon (list integer) ((ℤ.pos 10) ∷ (ℤ.pos 1) ∷ [])))) (UCon (tagCon bool false)))

expected-case-31 : Result
expected-case-31 = success (UCon (tagCon bytestring (mkByteString "\240\253")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-31 : Set
pending-case-31 = Pending (evalRaw test-case-31 ≡ expected-case-31)
```

## case-32

```
-- builtin/semantics/writeBits/case-32
test-case-32 : Untyped
test-case-32 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\244\255")))) (UCon (tagCon (list integer) ((ℤ.pos 10) ∷ (ℤ.pos 1) ∷ (ℤ.pos 10) ∷ (ℤ.pos 1) ∷ (ℤ.pos 1) ∷ (ℤ.pos 1) ∷ (ℤ.pos 1) ∷ (ℤ.pos 10) ∷ (ℤ.pos 10) ∷ (ℤ.pos 10) ∷ (ℤ.pos 1) ∷ (ℤ.pos 1) ∷ (ℤ.pos 1) ∷ (ℤ.pos 1) ∷ (ℤ.pos 1) ∷ (ℤ.pos 1) ∷ (ℤ.pos 10) ∷ (ℤ.pos 1) ∷ [])))) (UCon (tagCon bool false)))

expected-case-32 : Result
expected-case-32 = success (UCon (tagCon bytestring (mkByteString "\240\253")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-32 : Set
pending-case-32 = Pending (evalRaw test-case-32 ≡ expected-case-32)
```

## case-33

```
-- builtin/semantics/writeBits/case-33
test-case-33 : Untyped
test-case-33 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\244\255")))) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 10) ∷ (ℤ.pos 1) ∷ (ℤ.pos 10) ∷ (ℤ.pos 1) ∷ (ℤ.pos 10) ∷ (ℤ.pos 1) ∷ (ℤ.pos 10) ∷ (ℤ.pos 1) ∷ (ℤ.pos 10) ∷ (ℤ.pos 1) ∷ (ℤ.pos 10) ∷ (ℤ.pos 10) ∷ (ℤ.pos 10) ∷ (ℤ.pos 10) ∷ (ℤ.pos 11) ∷ (ℤ.pos 11) ∷ (ℤ.pos 9) ∷ [])))) (UCon (tagCon bool false)))

expected-case-33 : Result
expected-case-33 = success (UCon (tagCon bytestring (mkByteString "\240\253")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-33 : Set
pending-case-33 = Pending (evalRaw test-case-33 ≡ expected-case-33)
```

## case-34

```
-- builtin/semantics/writeBits/case-34
test-case-34 : Untyped
test-case-34 = (UApp (UApp (UApp (UBuiltin writeBits) (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL\255")))) (UCon (tagCon (list integer) ((ℤ.pos 10) ∷ [])))) (UCon (tagCon bool true)))) (UCon (tagCon (list integer) ((ℤ.pos 10) ∷ [])))) (UCon (tagCon bool false)))

expected-case-34 : Result
expected-case-34 = success (UCon (tagCon bytestring (mkByteString "\NUL\255")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-34 : Set
pending-case-34 = Pending (evalRaw test-case-34 ≡ expected-case-34)
```

## case-35

```
-- builtin/semantics/writeBits/case-35
test-case-35 : Untyped
test-case-35 = (UApp (UApp (UApp (UBuiltin writeBits) (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL\255")))) (UCon (tagCon (list integer) ((ℤ.pos 10) ∷ [])))) (UCon (tagCon bool false)))) (UCon (tagCon (list integer) ((ℤ.pos 10) ∷ [])))) (UCon (tagCon bool true)))

expected-case-35 : Result
expected-case-35 = success (UCon (tagCon bytestring (mkByteString "\EOT\255")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-35 : Set
pending-case-35 = Pending (evalRaw test-case-35 ≡ expected-case-35)
```

## case-36

```
-- builtin/semantics/writeBits/case-36
test-case-36 : Untyped
test-case-36 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ [])))) (UCon (tagCon bool true)))

expected-case-36 : Result
expected-case-36 = success (UCon (tagCon bytestring (mkByteString "\255")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-36 : Set
pending-case-36 = Pending (evalRaw test-case-36 ≡ expected-case-36)
```

## case-37

```
-- builtin/semantics/writeBits/case-37
test-case-37 : Untyped
test-case-37 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ [])))) (UCon (tagCon bool false)))

expected-case-37 : Result
expected-case-37 = success (UCon (tagCon bytestring (mkByteString "\NUL")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-37 : Set
pending-case-37 = Pending (evalRaw test-case-37 ≡ expected-case-37)
```

## case-38

```
-- builtin/semantics/writeBits/case-38
test-case-38 : Untyped
test-case-38 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 340) ∷ (ℤ.pos 342) ∷ (ℤ.pos 343) ∷ [])))) (UCon (tagCon bool true)))

expected-case-38 : Result
expected-case-38 = success (UCon (tagCon bytestring (mkByteString "\208\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-38 : Set
pending-case-38 = Pending (evalRaw test-case-38 ≡ expected-case-38)
```

## case-39

```
-- builtin/semantics/writeBits/case-39
-- Later updates to duplicate indices take precedence.
test-case-39 : Untyped
test-case-39 = (UApp (UApp (UApp (UBuiltin writeBits) (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 340) ∷ (ℤ.pos 342) ∷ (ℤ.pos 343) ∷ (ℤ.pos 340) ∷ (ℤ.pos 342) ∷ (ℤ.pos 343) ∷ [])))) (UCon (tagCon bool true)))) (UCon (tagCon (list integer) ((ℤ.pos 340) ∷ (ℤ.pos 342) ∷ (ℤ.pos 343) ∷ [])))) (UCon (tagCon bool false)))

expected-case-39 : Result
expected-case-39 = success (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-39 : Set
pending-case-39 = Pending (evalRaw test-case-39 ≡ expected-case-39)
```

## case-40

```
-- builtin/semantics/writeBits/case-40
test-case-40 : Untyped
test-case-40 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))) (UCon (tagCon (list integer) ((ℤ.pos 340) ∷ (ℤ.pos 342) ∷ (ℤ.pos 343) ∷ [])))) (UCon (tagCon bool false)))

expected-case-40 : Result
expected-case-40 = success (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-40 : Set
pending-case-40 = Pending (evalRaw test-case-40 ≡ expected-case-40)
```

## case-41

```
-- builtin/semantics/writeBits/case-41
-- An empty list of updates doesn't change anything.
test-case-41 : Untyped
test-case-41 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))) (UCon (tagCon (list integer) ([])))) (UCon (tagCon bool false)))

expected-case-41 : Result
expected-case-41 = success (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-41 : Set
pending-case-41 = Pending (evalRaw test-case-41 ≡ expected-case-41)
```

## case-42

```
-- builtin/semantics/writeBits/case-42
-- An empty list of updates doesn't change anything.
test-case-42 : Untyped
test-case-42 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))) (UCon (tagCon (list integer) ([])))) (UCon (tagCon bool true)))

expected-case-42 : Result
expected-case-42 = success (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-42 : Set
pending-case-42 = Pending (evalRaw test-case-42 ≡ expected-case-42)
```

## case-43

```
-- builtin/semantics/writeBits/case-43
-- An empty list of updates doesn't change anything.
test-case-43 : Untyped
test-case-43 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255")))) (UCon (tagCon (list integer) ([])))) (UCon (tagCon bool false)))

expected-case-43 : Result
expected-case-43 = success (UCon (tagCon bytestring (mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-43 : Set
pending-case-43 = Pending (evalRaw test-case-43 ≡ expected-case-43)
```

## case-44

```
-- builtin/semantics/writeBits/case-44
-- An empty list of updates doesn't change anything.
test-case-44 : Untyped
test-case-44 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255")))) (UCon (tagCon (list integer) ([])))) (UCon (tagCon bool true)))

expected-case-44 : Result
expected-case-44 = success (UCon (tagCon bytestring (mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-44 : Set
pending-case-44 = Pending (evalRaw test-case-44 ≡ expected-case-44)
```

## case-45

```
-- builtin/semantics/writeBits/case-45
-- We can apply an empty list of updates to the empty bytestring
test-case-45 : Untyped
test-case-45 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon (list integer) ([])))) (UCon (tagCon bool false)))

expected-case-45 : Result
expected-case-45 = success (UCon (tagCon bytestring (mkByteString "")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-45 : Set
pending-case-45 = Pending (evalRaw test-case-45 ≡ expected-case-45)
```

## case-46

```
-- builtin/semantics/writeBits/case-46
-- We can apply an empty list of updates to the empty bytestring
test-case-46 : Untyped
test-case-46 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon (list integer) ([])))) (UCon (tagCon bool true)))

expected-case-46 : Result
expected-case-46 = success (UCon (tagCon bytestring (mkByteString "")))

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-46 : Set
pending-case-46 = Pending (evalRaw test-case-46 ≡ expected-case-46)
```

## case-47

```
-- builtin/semantics/writeBits/case-47
-- Attempting to write to a negative position in the empty bytestring causes an error
test-case-47 : Untyped
test-case-47 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon (list integer) ((ℤ.negsuc 0) ∷ [])))) (UCon (tagCon bool false)))

expected-case-47 : Result
expected-case-47 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-47 : Set
pending-case-47 = Pending (evalRaw test-case-47 ≡ expected-case-47)
```

## case-48

```
-- builtin/semantics/writeBits/case-48
-- Attempting to write to a negative position in the empty bytestring causes an error
test-case-48 : Untyped
test-case-48 = (UApp (UApp (UApp (UBuiltin writeBits) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon (list integer) ((ℤ.negsuc 0) ∷ [])))) (UCon (tagCon bool true)))

expected-case-48 : Result
expected-case-48 = failure

-- Pending: bytestring constant; postulated builtin `writeBits`.
pending-case-48 : Set
pending-case-48 = Pending (evalRaw test-case-48 ≡ expected-case-48)
```
