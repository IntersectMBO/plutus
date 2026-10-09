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

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-01 : Set
pending-case-01 = Pending (evalRaw test-case-01 ≡ expected-case-01)
```

## case-02

```
-- builtin/semantics/shiftByteString/case-02
test-case-02 : Untyped
test-case-02 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon integer (ℤ.negsuc 2))))

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon bytestring (mkByteString "")))

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-02 : Set
pending-case-02 = Pending (evalRaw test-case-02 ≡ expected-case-02)
```

## case-03

```
-- builtin/semantics/shiftByteString/case-03
test-case-03 : Untyped
test-case-03 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "\235\252")))) (UCon (tagCon integer (ℤ.pos 5))))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon bytestring (mkByteString "\DEL\128")))

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-03 : Set
pending-case-03 = Pending (evalRaw test-case-03 ≡ expected-case-03)
```

## case-04

```
-- builtin/semantics/shiftByteString/case-04
test-case-04 : Untyped
test-case-04 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "\235\252")))) (UCon (tagCon integer (ℤ.negsuc 4))))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon bytestring (mkByteString "\a_")))

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-04 : Set
pending-case-04 = Pending (evalRaw test-case-04 ≡ expected-case-04)
```

## case-05

```
-- builtin/semantics/shiftByteString/case-05
test-case-05 : Untyped
test-case-05 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "\235\252")))) (UCon (tagCon integer (ℤ.pos 16))))

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon bytestring (mkByteString "\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-05 : Set
pending-case-05 = Pending (evalRaw test-case-05 ≡ expected-case-05)
```

## case-06

```
-- builtin/semantics/shiftByteString/case-06
test-case-06 : Untyped
test-case-06 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "\235\252")))) (UCon (tagCon integer (ℤ.negsuc 15))))

expected-case-06 : Result
expected-case-06 = success (UCon (tagCon bytestring (mkByteString "\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-06 : Set
pending-case-06 = Pending (evalRaw test-case-06 ≡ expected-case-06)
```

## case-07

```
-- builtin/semantics/shiftByteString/case-07
-- Shift by 0: the result should be the same as the input.
test-case-07 : Untyped
test-case-07 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 0))))

expected-case-07 : Result
expected-case-07 = success (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-07 : Set
pending-case-07 = Pending (evalRaw test-case-07 ≡ expected-case-07)
```

## case-08

```
-- builtin/semantics/shiftByteString/case-08
test-case-08 : Untyped
test-case-08 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 23))))

expected-case-08 : Result
expected-case-08 = success (UCon (tagCon bytestring (mkByteString "kB\194@\GS\206\224-\157\133\206^\179A\246\224g:\NAK\216L\171\176\159\"\n\129\STX\179\206\159\176\210\&3\217.c\172Q\216\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-08 : Set
pending-case-08 = Pending (evalRaw test-case-08 ≡ expected-case-08)
```

## case-09

```
-- builtin/semantics/shiftByteString/case-09
test-case-09 : Untyped
test-case-09 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.negsuc 22))))

expected-case-09 : Result
expected-case-09 = success (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NULg\133\225\173\v\t\NULw;\128\182v\ETB9z\205\a\219\129\156\232Wa2\174\194|\136*\EOT\n\207:~\195H\207d\185\142")))

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-09 : Set
pending-case-09 = Pending (evalRaw test-case-09 ≡ expected-case-09)
```

## case-10

```
-- builtin/semantics/shiftByteString/case-10
test-case-10 : Untyped
test-case-10 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 1000000))))

expected-case-10 : Result
expected-case-10 = success (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-10 : Set
pending-case-10 = Pending (evalRaw test-case-10 ≡ expected-case-10)
```

## case-11

```
-- builtin/semantics/shiftByteString/case-11
test-case-11 : Untyped
test-case-11 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.negsuc 999999))))

expected-case-11 : Result
expected-case-11 = success (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-11 : Set
pending-case-11 = Pending (evalRaw test-case-11 ≡ expected-case-11)
```

## case-12

```
-- builtin/semantics/shiftByteString/case-12
-- Shift by maxBound :: Int64
test-case-12 : Untyped
test-case-12 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 9223372036854775807))))

expected-case-12 : Result
expected-case-12 = success (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-12 : Set
pending-case-12 = Pending (evalRaw test-case-12 ≡ expected-case-12)
```

## case-13

```
-- builtin/semantics/shiftByteString/case-13
-- Shift by (maxBound :: Int64) + 1
test-case-13 : Untyped
test-case-13 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.pos 9223372036854775808))))

expected-case-13 : Result
expected-case-13 = failure

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-13 : Set
pending-case-13 = Pending (evalRaw test-case-13 ≡ expected-case-13)
```

## case-14

```
-- builtin/semantics/shiftByteString/case-14
-- Shift by minBound :: Int64
test-case-14 : Untyped
test-case-14 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.negsuc 9223372036854775807))))

expected-case-14 : Result
expected-case-14 = success (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL")))

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-14 : Set
pending-case-14 = Pending (evalRaw test-case-14 ≡ expected-case-14)
```

## case-15

```
-- builtin/semantics/shiftByteString/case-15
-- Shift by (minBound :: Int64) - 1
test-case-15 : Untyped
test-case-15 = (UApp (UApp (UBuiltin shiftByteString) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon integer (ℤ.negsuc 9223372036854775808))))

expected-case-15 : Result
expected-case-15 = failure

-- Pending: bytestring constant; postulated builtin `shiftByteString`.
pending-case-15 : Set
pending-case-15 = Pending (evalRaw test-case-15 ≡ expected-case-15)
```
