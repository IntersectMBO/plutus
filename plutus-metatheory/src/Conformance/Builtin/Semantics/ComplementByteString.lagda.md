---
title: Conformance.Builtin.Semantics.ComplementByteString
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/complementByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ComplementByteString where

open import Conformance.Eval
```

## case-01

```
-- builtin/semantics/complementByteString/case-01
test-case-01 : Untyped
test-case-01 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString ""))))

expected-case-01 : Result
expected-case-01 = success (UCon (tagCon bytestring (mkByteString "")))

-- Pending: bytestring constant; postulated builtin `complementByteString`.
pending-case-01 : Set
pending-case-01 = Pending (evalRaw test-case-01 ≡ expected-case-01)
```

## case-02

```
-- builtin/semantics/complementByteString/case-02
test-case-02 : Untyped
test-case-02 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString "\SI"))))

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon bytestring (mkByteString "\240")))

-- Pending: bytestring constant; postulated builtin `complementByteString`.
pending-case-02 : Set
pending-case-02 = Pending (evalRaw test-case-02 ≡ expected-case-02)
```

## case-03

```
-- builtin/semantics/complementByteString/case-03
test-case-03 : Untyped
test-case-03 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString "\176\v"))))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon bytestring (mkByteString "O\244")))

-- Pending: bytestring constant; postulated builtin `complementByteString`.
pending-case-03 : Set
pending-case-03 = Pending (evalRaw test-case-03 ≡ expected-case-03)
```

## case-04

```
-- builtin/semantics/complementByteString/case-04
test-case-04 : Untyped
test-case-04 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString "\219\156\134\FS\152\163\209\156\185(\194*2\170\174\nOt\SOH\DC3\220HsM<\NUL\SYNW\203\143\210\185I\DEL\175\SYN\164\f\RS\205\215\214X\ESCU\182%U:\243"))))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon bytestring (mkByteString "$cy\227g\\.cF\215=\213\205UQ\245\176\139\254\236#\183\140\178\195\255\233\168\&4p-F\182\128P\233[\243\225\&2()\167\228\170I\218\170\197\f")))

-- Pending: bytestring constant; postulated builtin `complementByteString`.
pending-case-04 : Set
pending-case-04 = Pending (evalRaw test-case-04 ≡ expected-case-04)
```

## case-05

```
-- builtin/semantics/complementByteString/case-05
test-case-05 : Untyped
test-case-05 = (UApp (ULambda (UApp (UApp (UBuiltin equalsByteString) (UVar 0)) (UApp (UBuiltin complementByteString) (UApp (UBuiltin complementByteString) (UVar 0))))) (UCon (tagCon bytestring (mkByteString "\219\156\134\FS\152\163\209\156\185(\194*2\170\174\nOt\SOH\DC3\220HsM<\NUL\SYNW\203\143\210\185I\DEL\175\SYN\164\f\RS\205\215\214X\ESCU\182%U:\243"))))

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon bool true))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `complementByteString`.
pending-case-05 : Set
pending-case-05 = Pending (evalRaw test-case-05 ≡ expected-case-05)
```
