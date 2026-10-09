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

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-01 : Set
pending-case-01 = Pending (evalRaw test-case-01 ≡ expected-case-01)
```

## case-02

```
-- builtin/semantics/readBit/case-02
test-case-02 : Untyped
test-case-02 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.pos 345))))

expected-case-02 : Result
expected-case-02 = failure

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-02 : Set
pending-case-02 = Pending (evalRaw test-case-02 ≡ expected-case-02)
```

## case-03

```
-- builtin/semantics/readBit/case-03
test-case-03 : Untyped
test-case-03 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.negsuc 0))))

expected-case-03 : Result
expected-case-03 = failure

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-03 : Set
pending-case-03 = Pending (evalRaw test-case-03 ≡ expected-case-03)
```

## case-04

```
-- builtin/semantics/readBit/case-04
test-case-04 : Untyped
test-case-04 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon integer (ℤ.negsuc 0))))

expected-case-04 : Result
expected-case-04 = failure

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-04 : Set
pending-case-04 = Pending (evalRaw test-case-04 ≡ expected-case-04)
```

## case-05

```
-- builtin/semantics/readBit/case-05
test-case-05 : Untyped
test-case-05 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 0))))

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-05 : Set
pending-case-05 = Pending (evalRaw test-case-05 ≡ expected-case-05)
```

## case-06

```
-- builtin/semantics/readBit/case-06
test-case-06 : Untyped
test-case-06 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 1))))

expected-case-06 : Result
expected-case-06 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-06 : Set
pending-case-06 = Pending (evalRaw test-case-06 ≡ expected-case-06)
```

## case-07

```
-- builtin/semantics/readBit/case-07
test-case-07 : Untyped
test-case-07 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 2))))

expected-case-07 : Result
expected-case-07 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-07 : Set
pending-case-07 = Pending (evalRaw test-case-07 ≡ expected-case-07)
```

## case-08

```
-- builtin/semantics/readBit/case-08
test-case-08 : Untyped
test-case-08 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 3))))

expected-case-08 : Result
expected-case-08 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-08 : Set
pending-case-08 = Pending (evalRaw test-case-08 ≡ expected-case-08)
```

## case-09

```
-- builtin/semantics/readBit/case-09
test-case-09 : Untyped
test-case-09 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 4))))

expected-case-09 : Result
expected-case-09 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-09 : Set
pending-case-09 = Pending (evalRaw test-case-09 ≡ expected-case-09)
```

## case-10

```
-- builtin/semantics/readBit/case-10
test-case-10 : Untyped
test-case-10 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 5))))

expected-case-10 : Result
expected-case-10 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-10 : Set
pending-case-10 = Pending (evalRaw test-case-10 ≡ expected-case-10)
```

## case-11

```
-- builtin/semantics/readBit/case-11
test-case-11 : Untyped
test-case-11 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 6))))

expected-case-11 : Result
expected-case-11 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-11 : Set
pending-case-11 = Pending (evalRaw test-case-11 ≡ expected-case-11)
```

## case-12

```
-- builtin/semantics/readBit/case-12
test-case-12 : Untyped
test-case-12 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 7))))

expected-case-12 : Result
expected-case-12 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-12 : Set
pending-case-12 = Pending (evalRaw test-case-12 ≡ expected-case-12)
```

## case-13

```
-- builtin/semantics/readBit/case-13
test-case-13 : Untyped
test-case-13 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244")))) (UCon (tagCon integer (ℤ.pos 8))))

expected-case-13 : Result
expected-case-13 = failure

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-13 : Set
pending-case-13 = Pending (evalRaw test-case-13 ≡ expected-case-13)
```

## case-14

```
-- builtin/semantics/readBit/case-14
test-case-14 : Untyped
test-case-14 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\255\244")))) (UCon (tagCon integer (ℤ.pos 16))))

expected-case-14 : Result
expected-case-14 = failure

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-14 : Set
pending-case-14 = Pending (evalRaw test-case-14 ≡ expected-case-14)
```

## case-15

```
-- builtin/semantics/readBit/case-15
test-case-15 : Untyped
test-case-15 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "\244\255")))) (UCon (tagCon integer (ℤ.pos 10))))

expected-case-15 : Result
expected-case-15 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-15 : Set
pending-case-15 = Pending (evalRaw test-case-15 ≡ expected-case-15)
```

## case-16

```
-- builtin/semantics/readBit/case-16
test-case-16 : Untyped
test-case-16 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 341))))

expected-case-16 : Result
expected-case-16 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-16 : Set
pending-case-16 = Pending (evalRaw test-case-16 ≡ expected-case-16)
```

## case-17

```
-- builtin/semantics/readBit/case-17
test-case-17 : Untyped
test-case-17 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 343))))

expected-case-17 : Result
expected-case-17 = success (UCon (tagCon bool false))

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-17 : Set
pending-case-17 = Pending (evalRaw test-case-17 ≡ expected-case-17)
```

## case-18

```
-- builtin/semantics/readBit/case-18
test-case-18 : Untyped
test-case-18 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 344))))

expected-case-18 : Result
expected-case-18 = failure

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-18 : Set
pending-case-18 = Pending (evalRaw test-case-18 ≡ expected-case-18)
```

## case-19

```
-- builtin/semantics/readBit/case-19
test-case-19 : Untyped
test-case-19 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 9223372036854775807))))

expected-case-19 : Result
expected-case-19 = failure

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-19 : Set
pending-case-19 = Pending (evalRaw test-case-19 ≡ expected-case-19)
```

## case-20

```
-- builtin/semantics/readBit/case-20
test-case-20 : Untyped
test-case-20 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 9223372036854775808))))

expected-case-20 : Result
expected-case-20 = failure

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-20 : Set
pending-case-20 = Pending (evalRaw test-case-20 ≡ expected-case-20)
```

## case-21

```
-- builtin/semantics/readBit/case-21
test-case-21 : Untyped
test-case-21 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.negsuc 9223372036854775807))))

expected-case-21 : Result
expected-case-21 = failure

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-21 : Set
pending-case-21 = Pending (evalRaw test-case-21 ≡ expected-case-21)
```

## case-22

```
-- builtin/semantics/readBit/case-22
test-case-22 : Untyped
test-case-22 = (UApp (UApp (UBuiltin readBit) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.negsuc 9223372036854775808))))

expected-case-22 : Result
expected-case-22 = failure

-- Pending: bytestring constant; postulated builtin `readBit`.
pending-case-22 : Set
pending-case-22 = Pending (evalRaw test-case-22 ≡ expected-case-22)
```
