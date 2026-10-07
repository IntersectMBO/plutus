---
title: Conformance.Builtin.Semantics.DropList
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/dropList`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.DropList where

open import Conformance.Eval
```

## dropList-01

```
-- builtin/semantics/dropList/dropList-01
-- Dropping zero elements has no effect.
test-dropList-01 : Untyped
test-dropList-01 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon (list integer) ((ℤ.pos 11) ∷ (ℤ.pos 22) ∷ (ℤ.pos 33) ∷ (ℤ.pos 44) ∷ (ℤ.pos 55) ∷ (ℤ.pos 66) ∷ (ℤ.pos 77) ∷ (ℤ.pos 88) ∷ (ℤ.pos 99) ∷ []))))

expected-dropList-01 : Result
expected-dropList-01 = success (UCon (tagCon (list integer) ((ℤ.pos 11) ∷ (ℤ.pos 22) ∷ (ℤ.pos 33) ∷ (ℤ.pos 44) ∷ (ℤ.pos 55) ∷ (ℤ.pos 66) ∷ (ℤ.pos 77) ∷ (ℤ.pos 88) ∷ (ℤ.pos 99) ∷ [])))

_ : evalRaw test-dropList-01 ≡ expected-dropList-01
_ = refl
```

## dropList-02

```
-- builtin/semantics/dropList/dropList-02
-- Dropping zero elements has no effect.
test-dropList-02 : Untyped
test-dropList-02 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon (list bytestring) ((mkByteString "\DC24V") ∷ (mkByteString "#Eg") ∷ (mkByteString "4Vx") ∷ (mkByteString "Eg\137") ∷ (mkByteString "Vx\154") ∷ (mkByteString "g\137\171") ∷ (mkByteString "x\154\188") ∷ (mkByteString "\137\171\205\147#$y\ETB4\ETB\130O\255") ∷ (mkByteString "\255\238\255\238\255\238") ∷ []))))

expected-dropList-02 : Result
expected-dropList-02 = success (UCon (tagCon (list bytestring) ((mkByteString "\DC24V") ∷ (mkByteString "#Eg") ∷ (mkByteString "4Vx") ∷ (mkByteString "Eg\137") ∷ (mkByteString "Vx\154") ∷ (mkByteString "g\137\171") ∷ (mkByteString "x\154\188") ∷ (mkByteString "\137\171\205\147#$y\ETB4\ETB\130O\255") ∷ (mkByteString "\255\238\255\238\255\238") ∷ [])))

-- Pending: bytestring constant.
pending-dropList-02 : Set
pending-dropList-02 = Pending (evalRaw test-dropList-02 ≡ expected-dropList-02)
```

## dropList-03

```
-- builtin/semantics/dropList/dropList-03
-- A typical case where you really drop some elements.
test-dropList-03 : Untyped
test-dropList-03 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.pos 7)))) (UCon (tagCon (list integer) ((ℤ.pos 11) ∷ (ℤ.pos 22) ∷ (ℤ.pos 33) ∷ (ℤ.pos 44) ∷ (ℤ.pos 55) ∷ (ℤ.pos 66) ∷ (ℤ.pos 77) ∷ (ℤ.pos 88) ∷ (ℤ.pos 99) ∷ []))))

expected-dropList-03 : Result
expected-dropList-03 = success (UCon (tagCon (list integer) ((ℤ.pos 88) ∷ (ℤ.pos 99) ∷ [])))

_ : evalRaw test-dropList-03 ≡ expected-dropList-03
_ = refl
```

## dropList-04

```
-- builtin/semantics/dropList/dropList-04
-- A typical case where you really drop some elements.
test-dropList-04 : Untyped
test-dropList-04 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.pos 7)))) (UCon (tagCon (list bytestring) ((mkByteString "\DC24V") ∷ (mkByteString "#Eg") ∷ (mkByteString "4Vx") ∷ (mkByteString "Eg\137") ∷ (mkByteString "Vx\154") ∷ (mkByteString "g\137\171") ∷ (mkByteString "x\154\188") ∷ (mkByteString "\137\171\205\147#$y\ETB4\ETB\130O\255") ∷ (mkByteString "\255\238\255\238\255\238") ∷ []))))

expected-dropList-04 : Result
expected-dropList-04 = success (UCon (tagCon (list bytestring) ((mkByteString "\137\171\205\147#$y\ETB4\ETB\130O\255") ∷ (mkByteString "\255\238\255\238\255\238") ∷ [])))

-- Pending: bytestring constant.
pending-dropList-04 : Set
pending-dropList-04 = Pending (evalRaw test-dropList-04 ≡ expected-dropList-04)
```

## dropList-05

```
-- builtin/semantics/dropList/dropList-05
-- Dropping more elements than the length of the list succeeds and returns the
-- empty list.
test-dropList-05 : Untyped
test-dropList-05 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.pos 17)))) (UCon (tagCon (list integer) ((ℤ.pos 11) ∷ (ℤ.pos 22) ∷ (ℤ.pos 33) ∷ (ℤ.pos 44) ∷ (ℤ.pos 55) ∷ (ℤ.pos 66) ∷ (ℤ.pos 77) ∷ (ℤ.pos 88) ∷ (ℤ.pos 99) ∷ []))))

expected-dropList-05 : Result
expected-dropList-05 = success (UCon (tagCon (list integer) ([])))

_ : evalRaw test-dropList-05 ≡ expected-dropList-05
_ = refl
```

## dropList-06

```
-- builtin/semantics/dropList/dropList-06
-- Dropping more elements than the length of the list succeeds and returns the
-- empty list.
test-dropList-06 : Untyped
test-dropList-06 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.pos 17)))) (UCon (tagCon (list bytestring) ((mkByteString "\DC24V") ∷ (mkByteString "#Eg") ∷ (mkByteString "4Vx") ∷ (mkByteString "Eg\137") ∷ (mkByteString "Vx\154") ∷ (mkByteString "g\137\171") ∷ (mkByteString "x\154\188") ∷ (mkByteString "\137\171\205\147#$y\ETB4\ETB\130O\255") ∷ (mkByteString "\255\238\255\238\255\238") ∷ []))))

expected-dropList-06 : Result
expected-dropList-06 = success (UCon (tagCon (list bytestring) ([])))

-- Pending: bytestring constant.
pending-dropList-06 : Set
pending-dropList-06 = Pending (evalRaw test-dropList-06 ≡ expected-dropList-06)
```

## dropList-07

```
-- builtin/semantics/dropList/dropList-07
-- Dropping a negative number of elements succeeds and returns the list unchanged.
test-dropList-07 : Untyped
test-dropList-07 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.negsuc 6)))) (UCon (tagCon (list integer) ((ℤ.pos 11) ∷ (ℤ.pos 22) ∷ (ℤ.pos 33) ∷ (ℤ.pos 44) ∷ (ℤ.pos 55) ∷ (ℤ.pos 66) ∷ (ℤ.pos 77) ∷ (ℤ.pos 88) ∷ (ℤ.pos 99) ∷ []))))

expected-dropList-07 : Result
expected-dropList-07 = success (UCon (tagCon (list integer) ((ℤ.pos 11) ∷ (ℤ.pos 22) ∷ (ℤ.pos 33) ∷ (ℤ.pos 44) ∷ (ℤ.pos 55) ∷ (ℤ.pos 66) ∷ (ℤ.pos 77) ∷ (ℤ.pos 88) ∷ (ℤ.pos 99) ∷ [])))

_ : evalRaw test-dropList-07 ≡ expected-dropList-07
_ = refl
```

## dropList-08

```
-- builtin/semantics/dropList/dropList-08
-- Dropping a negative number of elements succeeds and returns the list unchanged.
test-dropList-08 : Untyped
test-dropList-08 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.negsuc 6)))) (UCon (tagCon (list bytestring) ((mkByteString "\DC24V") ∷ (mkByteString "#Eg") ∷ (mkByteString "4Vx") ∷ (mkByteString "Eg\137") ∷ (mkByteString "Vx\154") ∷ (mkByteString "g\137\171") ∷ (mkByteString "x\154\188") ∷ (mkByteString "\137\171\205\147#$y\ETB4\ETB\130O\255") ∷ (mkByteString "\255\238\255\238\255\238") ∷ []))))

expected-dropList-08 : Result
expected-dropList-08 = success (UCon (tagCon (list bytestring) ((mkByteString "\DC24V") ∷ (mkByteString "#Eg") ∷ (mkByteString "4Vx") ∷ (mkByteString "Eg\137") ∷ (mkByteString "Vx\154") ∷ (mkByteString "g\137\171") ∷ (mkByteString "x\154\188") ∷ (mkByteString "\137\171\205\147#$y\ETB4\ETB\130O\255") ∷ (mkByteString "\255\238\255\238\255\238") ∷ [])))

-- Pending: bytestring constant.
pending-dropList-08 : Set
pending-dropList-08 = Pending (evalRaw test-dropList-08 ≡ expected-dropList-08)
```

## dropList-09

```
-- builtin/semantics/dropList/dropList-09
-- This should return the empty list.  However, if run in restricting mode it
-- will (probably, depending on the cost model) attempt to consume the maxmimum
-- budget and fail because the cost depends on how many elements you want to
-- drop, irrespective of the size of the list.
test-dropList-09 : Untyped
test-dropList-09 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.pos 10000000000000000000)))) (UCon (tagCon (list integer) ((ℤ.pos 11) ∷ (ℤ.pos 22) ∷ (ℤ.pos 33) ∷ (ℤ.pos 44) ∷ (ℤ.pos 55) ∷ (ℤ.pos 66) ∷ (ℤ.pos 77) ∷ (ℤ.pos 88) ∷ (ℤ.pos 99) ∷ []))))

expected-dropList-09 : Result
expected-dropList-09 = success (UCon (tagCon (list integer) ([])))

_ : evalRaw test-dropList-09 ≡ expected-dropList-09
_ = refl
```

## dropList-10

```
-- builtin/semantics/dropList/dropList-10
-- This should return the empty list.  However, if run in restricting mode it
-- will (probably, depending on the cost model) attempt to consume the maxmimum
-- budget and fail because the cost depends on how many elements you want to
-- drop, irrespective of the size of the list.
test-dropList-10 : Untyped
test-dropList-10 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.negsuc 12345678901234567889)))) (UCon (tagCon (list integer) ((ℤ.pos 11) ∷ (ℤ.pos 22) ∷ (ℤ.pos 33) ∷ (ℤ.pos 44) ∷ (ℤ.pos 55) ∷ (ℤ.pos 66) ∷ (ℤ.pos 77) ∷ (ℤ.pos 88) ∷ (ℤ.pos 99) ∷ []))))

expected-dropList-10 : Result
expected-dropList-10 = success (UCon (tagCon (list integer) ((ℤ.pos 11) ∷ (ℤ.pos 22) ∷ (ℤ.pos 33) ∷ (ℤ.pos 44) ∷ (ℤ.pos 55) ∷ (ℤ.pos 66) ∷ (ℤ.pos 77) ∷ (ℤ.pos 88) ∷ (ℤ.pos 99) ∷ [])))

_ : evalRaw test-dropList-10 ≡ expected-dropList-10
_ = refl
```

## dropList-11

```
-- builtin/semantics/dropList/dropList-11
-- Dropping any number of elements from an empty list always succeeds (and
-- returns the empty list).
test-dropList-11 : Untyped
test-dropList-11 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.negsuc 1233)))) (UCon (tagCon (list (pair bool string)) ([]))))

expected-dropList-11 : Result
expected-dropList-11 = success (UCon (tagCon (list (pair bool string)) ([])))

_ : evalRaw test-dropList-11 ≡ expected-dropList-11
_ = refl
```

## dropList-12

```
-- builtin/semantics/dropList/dropList-12
-- Dropping any number of elements from an empty list always succeeds (and
-- returns the empty list).
test-dropList-12 : Untyped
test-dropList-12 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon (list (pair unit integer)) ([]))))

expected-dropList-12 : Result
expected-dropList-12 = success (UCon (tagCon (list (pair unit integer)) ([])))

_ : evalRaw test-dropList-12 ≡ expected-dropList-12
_ = refl
```

## dropList-13

```
-- builtin/semantics/dropList/dropList-13
-- Dropping any number of elements from an empty list always succeeds (and
-- returns the empty list).
test-dropList-13 : Untyped
test-dropList-13 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.pos 1234)))) (UCon (tagCon (list (pair (list integer) unit)) ([]))))

expected-dropList-13 : Result
expected-dropList-13 = success (UCon (tagCon (list (pair (list integer) unit)) ([])))

_ : evalRaw test-dropList-13 ≡ expected-dropList-13
_ = refl
```

## dropList-14

```
-- builtin/semantics/dropList/dropList-14
-- Drop (maxBound::Int)-1 elements
test-dropList-14 : Untyped
test-dropList-14 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.pos 9223372036854775806)))) (UCon (tagCon (list integer) ((ℤ.pos 20) ∷ (ℤ.pos 21) ∷ (ℤ.pos 22) ∷ (ℤ.pos 23) ∷ (ℤ.pos 24) ∷ (ℤ.pos 25) ∷ (ℤ.pos 26) ∷ (ℤ.pos 27) ∷ (ℤ.pos 28) ∷ (ℤ.pos 29) ∷ (ℤ.pos 30) ∷ (ℤ.pos 31) ∷ (ℤ.pos 32) ∷ (ℤ.pos 33) ∷ (ℤ.pos 34) ∷ (ℤ.pos 35) ∷ (ℤ.pos 36) ∷ (ℤ.pos 37) ∷ (ℤ.pos 38) ∷ (ℤ.pos 39) ∷ (ℤ.pos 40) ∷ (ℤ.pos 41) ∷ (ℤ.pos 42) ∷ (ℤ.pos 43) ∷ (ℤ.pos 44) ∷ (ℤ.pos 45) ∷ (ℤ.pos 46) ∷ (ℤ.pos 47) ∷ (ℤ.pos 48) ∷ (ℤ.pos 49) ∷ (ℤ.pos 50) ∷ (ℤ.pos 51) ∷ (ℤ.pos 52) ∷ (ℤ.pos 53) ∷ (ℤ.pos 54) ∷ (ℤ.pos 55) ∷ (ℤ.pos 56) ∷ (ℤ.pos 57) ∷ (ℤ.pos 58) ∷ (ℤ.pos 59) ∷ (ℤ.pos 60) ∷ (ℤ.pos 61) ∷ (ℤ.pos 62) ∷ (ℤ.pos 63) ∷ (ℤ.pos 64) ∷ (ℤ.pos 65) ∷ (ℤ.pos 66) ∷ (ℤ.pos 67) ∷ (ℤ.pos 68) ∷ (ℤ.pos 69) ∷ (ℤ.pos 70) ∷ (ℤ.pos 71) ∷ (ℤ.pos 72) ∷ (ℤ.pos 73) ∷ (ℤ.pos 74) ∷ (ℤ.pos 75) ∷ (ℤ.pos 76) ∷ (ℤ.pos 77) ∷ (ℤ.pos 78) ∷ (ℤ.pos 79) ∷ (ℤ.pos 80) ∷ (ℤ.pos 81) ∷ (ℤ.pos 82) ∷ (ℤ.pos 83) ∷ (ℤ.pos 84) ∷ (ℤ.pos 85) ∷ (ℤ.pos 86) ∷ (ℤ.pos 87) ∷ (ℤ.pos 88) ∷ (ℤ.pos 89) ∷ (ℤ.pos 90) ∷ (ℤ.pos 91) ∷ (ℤ.pos 92) ∷ (ℤ.pos 93) ∷ (ℤ.pos 94) ∷ (ℤ.pos 95) ∷ (ℤ.pos 96) ∷ (ℤ.pos 97) ∷ (ℤ.pos 98) ∷ (ℤ.pos 99) ∷ (ℤ.pos 100) ∷ (ℤ.pos 101) ∷ (ℤ.pos 102) ∷ (ℤ.pos 103) ∷ (ℤ.pos 104) ∷ (ℤ.pos 105) ∷ (ℤ.pos 106) ∷ (ℤ.pos 107) ∷ (ℤ.pos 108) ∷ (ℤ.pos 109) ∷ (ℤ.pos 110) ∷ (ℤ.pos 111) ∷ []))))

expected-dropList-14 : Result
expected-dropList-14 = success (UCon (tagCon (list integer) ([])))

_ : evalRaw test-dropList-14 ≡ expected-dropList-14
_ = refl
```

## dropList-15

```
-- builtin/semantics/dropList/dropList-15
-- Drop (maxBound::Int) elements
test-dropList-15 : Untyped
test-dropList-15 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.pos 9223372036854775807)))) (UCon (tagCon (list integer) ((ℤ.pos 20) ∷ (ℤ.pos 21) ∷ (ℤ.pos 22) ∷ (ℤ.pos 23) ∷ (ℤ.pos 24) ∷ (ℤ.pos 25) ∷ (ℤ.pos 26) ∷ (ℤ.pos 27) ∷ (ℤ.pos 28) ∷ (ℤ.pos 29) ∷ (ℤ.pos 30) ∷ (ℤ.pos 31) ∷ (ℤ.pos 32) ∷ (ℤ.pos 33) ∷ (ℤ.pos 34) ∷ (ℤ.pos 35) ∷ (ℤ.pos 36) ∷ (ℤ.pos 37) ∷ (ℤ.pos 38) ∷ (ℤ.pos 39) ∷ (ℤ.pos 40) ∷ (ℤ.pos 41) ∷ (ℤ.pos 42) ∷ (ℤ.pos 43) ∷ (ℤ.pos 44) ∷ (ℤ.pos 45) ∷ (ℤ.pos 46) ∷ (ℤ.pos 47) ∷ (ℤ.pos 48) ∷ (ℤ.pos 49) ∷ (ℤ.pos 50) ∷ (ℤ.pos 51) ∷ (ℤ.pos 52) ∷ (ℤ.pos 53) ∷ (ℤ.pos 54) ∷ (ℤ.pos 55) ∷ (ℤ.pos 56) ∷ (ℤ.pos 57) ∷ (ℤ.pos 58) ∷ (ℤ.pos 59) ∷ (ℤ.pos 60) ∷ (ℤ.pos 61) ∷ (ℤ.pos 62) ∷ (ℤ.pos 63) ∷ (ℤ.pos 64) ∷ (ℤ.pos 65) ∷ (ℤ.pos 66) ∷ (ℤ.pos 67) ∷ (ℤ.pos 68) ∷ (ℤ.pos 69) ∷ (ℤ.pos 70) ∷ (ℤ.pos 71) ∷ (ℤ.pos 72) ∷ (ℤ.pos 73) ∷ (ℤ.pos 74) ∷ (ℤ.pos 75) ∷ (ℤ.pos 76) ∷ (ℤ.pos 77) ∷ (ℤ.pos 78) ∷ (ℤ.pos 79) ∷ (ℤ.pos 80) ∷ (ℤ.pos 81) ∷ (ℤ.pos 82) ∷ (ℤ.pos 83) ∷ (ℤ.pos 84) ∷ (ℤ.pos 85) ∷ (ℤ.pos 86) ∷ (ℤ.pos 87) ∷ (ℤ.pos 88) ∷ (ℤ.pos 89) ∷ (ℤ.pos 90) ∷ (ℤ.pos 91) ∷ (ℤ.pos 92) ∷ (ℤ.pos 93) ∷ (ℤ.pos 94) ∷ (ℤ.pos 95) ∷ (ℤ.pos 96) ∷ (ℤ.pos 97) ∷ (ℤ.pos 98) ∷ (ℤ.pos 99) ∷ (ℤ.pos 100) ∷ (ℤ.pos 101) ∷ (ℤ.pos 102) ∷ (ℤ.pos 103) ∷ (ℤ.pos 104) ∷ (ℤ.pos 105) ∷ (ℤ.pos 106) ∷ (ℤ.pos 107) ∷ (ℤ.pos 108) ∷ (ℤ.pos 109) ∷ (ℤ.pos 110) ∷ (ℤ.pos 111) ∷ []))))

expected-dropList-15 : Result
expected-dropList-15 = success (UCon (tagCon (list integer) ([])))

_ : evalRaw test-dropList-15 ≡ expected-dropList-15
_ = refl
```

## dropList-16

```
-- builtin/semantics/dropList/dropList-16
-- Drop (maxBound::Int)+1 elements
test-dropList-16 : Untyped
test-dropList-16 = (UApp (UApp (UForce (UBuiltin dropList)) (UCon (tagCon integer (ℤ.pos 9223372036854775808)))) (UCon (tagCon (list integer) ((ℤ.pos 20) ∷ (ℤ.pos 21) ∷ (ℤ.pos 22) ∷ (ℤ.pos 23) ∷ (ℤ.pos 24) ∷ (ℤ.pos 25) ∷ (ℤ.pos 26) ∷ (ℤ.pos 27) ∷ (ℤ.pos 28) ∷ (ℤ.pos 29) ∷ (ℤ.pos 30) ∷ (ℤ.pos 31) ∷ (ℤ.pos 32) ∷ (ℤ.pos 33) ∷ (ℤ.pos 34) ∷ (ℤ.pos 35) ∷ (ℤ.pos 36) ∷ (ℤ.pos 37) ∷ (ℤ.pos 38) ∷ (ℤ.pos 39) ∷ (ℤ.pos 40) ∷ (ℤ.pos 41) ∷ (ℤ.pos 42) ∷ (ℤ.pos 43) ∷ (ℤ.pos 44) ∷ (ℤ.pos 45) ∷ (ℤ.pos 46) ∷ (ℤ.pos 47) ∷ (ℤ.pos 48) ∷ (ℤ.pos 49) ∷ (ℤ.pos 50) ∷ (ℤ.pos 51) ∷ (ℤ.pos 52) ∷ (ℤ.pos 53) ∷ (ℤ.pos 54) ∷ (ℤ.pos 55) ∷ (ℤ.pos 56) ∷ (ℤ.pos 57) ∷ (ℤ.pos 58) ∷ (ℤ.pos 59) ∷ (ℤ.pos 60) ∷ (ℤ.pos 61) ∷ (ℤ.pos 62) ∷ (ℤ.pos 63) ∷ (ℤ.pos 64) ∷ (ℤ.pos 65) ∷ (ℤ.pos 66) ∷ (ℤ.pos 67) ∷ (ℤ.pos 68) ∷ (ℤ.pos 69) ∷ (ℤ.pos 70) ∷ (ℤ.pos 71) ∷ (ℤ.pos 72) ∷ (ℤ.pos 73) ∷ (ℤ.pos 74) ∷ (ℤ.pos 75) ∷ (ℤ.pos 76) ∷ (ℤ.pos 77) ∷ (ℤ.pos 78) ∷ (ℤ.pos 79) ∷ (ℤ.pos 80) ∷ (ℤ.pos 81) ∷ (ℤ.pos 82) ∷ (ℤ.pos 83) ∷ (ℤ.pos 84) ∷ (ℤ.pos 85) ∷ (ℤ.pos 86) ∷ (ℤ.pos 87) ∷ (ℤ.pos 88) ∷ (ℤ.pos 89) ∷ (ℤ.pos 90) ∷ (ℤ.pos 91) ∷ (ℤ.pos 92) ∷ (ℤ.pos 93) ∷ (ℤ.pos 94) ∷ (ℤ.pos 95) ∷ (ℤ.pos 96) ∷ (ℤ.pos 97) ∷ (ℤ.pos 98) ∷ (ℤ.pos 99) ∷ (ℤ.pos 100) ∷ (ℤ.pos 101) ∷ (ℤ.pos 102) ∷ (ℤ.pos 103) ∷ (ℤ.pos 104) ∷ (ℤ.pos 105) ∷ (ℤ.pos 106) ∷ (ℤ.pos 107) ∷ (ℤ.pos 108) ∷ (ℤ.pos 109) ∷ (ℤ.pos 110) ∷ (ℤ.pos 111) ∷ []))))

expected-dropList-16 : Result
expected-dropList-16 = success (UCon (tagCon (list integer) ([])))

_ : evalRaw test-dropList-16 ≡ expected-dropList-16
_ = refl
```
