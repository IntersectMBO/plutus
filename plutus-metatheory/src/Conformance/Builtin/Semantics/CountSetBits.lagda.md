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

-- Pending: bytestring constant; postulated builtin `countSetBits`.
pending-case-01 : Set
pending-case-01 = Pending (evalRaw test-case-01 ≡ expected-case-01)
```

## case-02

```
-- builtin/semantics/countSetBits/case-02
test-case-02 : Untyped
test-case-02 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "\NUL\NUL"))))

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: bytestring constant; postulated builtin `countSetBits`.
pending-case-02 : Set
pending-case-02 = Pending (evalRaw test-case-02 ≡ expected-case-02)
```

## case-03

```
-- builtin/semantics/countSetBits/case-03
test-case-03 : Untyped
test-case-03 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "\SOH\NUL"))))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: bytestring constant; postulated builtin `countSetBits`.
pending-case-03 : Set
pending-case-03 = Pending (evalRaw test-case-03 ≡ expected-case-03)
```

## case-04

```
-- builtin/semantics/countSetBits/case-04
test-case-04 : Untyped
test-case-04 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "\NUL\SOH"))))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: bytestring constant; postulated builtin `countSetBits`.
pending-case-04 : Set
pending-case-04 = Pending (evalRaw test-case-04 ≡ expected-case-04)
```

## case-05

```
-- builtin/semantics/countSetBits/case-05
test-case-05 : Untyped
test-case-05 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176"))))

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon integer (ℤ.pos 163)))

-- Pending: bytestring constant; postulated builtin `countSetBits`.
pending-case-05 : Set
pending-case-05 = Pending (evalRaw test-case-05 ≡ expected-case-05)
```

## case-06

```
-- builtin/semantics/countSetBits/case-06
test-case-06 : Untyped
test-case-06 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))

expected-case-06 : Result
expected-case-06 = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: bytestring constant; postulated builtin `countSetBits`.
pending-case-06 : Set
pending-case-06 = Pending (evalRaw test-case-06 ≡ expected-case-06)
```

## case-07

```
-- builtin/semantics/countSetBits/case-07
test-case-07 : Untyped
test-case-07 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "\NUL\NUL\NUL\NUL\NUL\NUL\NUL\DLE\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL\NUL"))))

expected-case-07 : Result
expected-case-07 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: bytestring constant; postulated builtin `countSetBits`.
pending-case-07 : Set
pending-case-07 = Pending (evalRaw test-case-07 ≡ expected-case-07)
```

## case-08

```
-- builtin/semantics/countSetBits/case-08
test-case-08 : Untyped
test-case-08 = (UApp (UBuiltin countSetBits) (UCon (tagCon bytestring (mkByteString "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255"))))

expected-case-08 : Result
expected-case-08 = success (UCon (tagCon integer (ℤ.pos 344)))

-- Pending: bytestring constant; postulated builtin `countSetBits`.
pending-case-08 : Set
pending-case-08 = Pending (evalRaw test-case-08 ≡ expected-case-08)
```
