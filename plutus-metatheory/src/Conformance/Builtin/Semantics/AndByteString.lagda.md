---
title: Conformance.Builtin.Semantics.AndByteString
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/andByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.AndByteString where

open import Conformance.Eval
```

## case-01

```
-- builtin/semantics/andByteString/case-01
test-case-01 : Untyped
test-case-01 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "\255"))))

expected-case-01 : Result
expected-case-01 = success (UCon (tagCon bytestring (mkByteString "")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-01 : Set
pending-case-01 = Pending (evalRaw test-case-01 ≡ expected-case-01)
```

## case-02

```
-- builtin/semantics/andByteString/case-02
test-case-02 : Untyped
test-case-02 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon bytestring (mkByteString ""))))

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon bytestring (mkByteString "")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-02 : Set
pending-case-02 = Pending (evalRaw test-case-02 ≡ expected-case-02)
```

## case-03

```
-- builtin/semantics/andByteString/case-03
test-case-03 : Untyped
test-case-03 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon bytestring (mkByteString "\NUL"))))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon bytestring (mkByteString "\NUL")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-03 : Set
pending-case-03 = Pending (evalRaw test-case-03 ≡ expected-case-03)
```

## case-04

```
-- builtin/semantics/andByteString/case-04
test-case-04 : Untyped
test-case-04 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon bytestring (mkByteString "\255"))))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon bytestring (mkByteString "\NUL")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-04 : Set
pending-case-04 = Pending (evalRaw test-case-04 ≡ expected-case-04)
```

## case-05

```
-- builtin/semantics/andByteString/case-05
test-case-05 : Untyped
test-case-05 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "O\NUL")))) (UCon (tagCon bytestring (mkByteString "\244"))))

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon bytestring (mkByteString "D")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-05 : Set
pending-case-05 = Pending (evalRaw test-case-05 ≡ expected-case-05)
```

## case-06

```
-- builtin/semantics/andByteString/case-06
test-case-06 : Untyped
test-case-06 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "\255"))))

expected-case-06 : Result
expected-case-06 = success (UCon (tagCon bytestring (mkByteString "\255")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-06 : Set
pending-case-06 = Pending (evalRaw test-case-06 ≡ expected-case-06)
```

## case-07

```
-- builtin/semantics/andByteString/case-07
test-case-07 : Untyped
test-case-07 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon bytestring (mkByteString ""))))

expected-case-07 : Result
expected-case-07 = success (UCon (tagCon bytestring (mkByteString "\255")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-07 : Set
pending-case-07 = Pending (evalRaw test-case-07 ≡ expected-case-07)
```

## case-08

```
-- builtin/semantics/andByteString/case-08
test-case-08 : Untyped
test-case-08 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon bytestring (mkByteString "\NUL"))))

expected-case-08 : Result
expected-case-08 = success (UCon (tagCon bytestring (mkByteString "\NUL")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-08 : Set
pending-case-08 = Pending (evalRaw test-case-08 ≡ expected-case-08)
```

## case-09

```
-- builtin/semantics/andByteString/case-09
test-case-09 : Untyped
test-case-09 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon bytestring (mkByteString "\255"))))

expected-case-09 : Result
expected-case-09 = success (UCon (tagCon bytestring (mkByteString "\NUL")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-09 : Set
pending-case-09 = Pending (evalRaw test-case-09 ≡ expected-case-09)
```

## case-10

```
-- builtin/semantics/andByteString/case-10
test-case-10 : Untyped
test-case-10 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "O\NUL")))) (UCon (tagCon bytestring (mkByteString "\244"))))

expected-case-10 : Result
expected-case-10 = success (UCon (tagCon bytestring (mkByteString "D\NUL")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-10 : Set
pending-case-10 = Pending (evalRaw test-case-10 ≡ expected-case-10)
```

## case-11

```
-- builtin/semantics/andByteString/case-11
test-case-11 : Untyped
test-case-11 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon bytestring (mkByteString "\219\156\134\FS\152\163\209\156\185(\194*2\170\174\nOt\SOH\DC3\220HsM<\NUL\SYNW\203\143\210\185I\DEL\175\SYN\164\f\RS\205\215\214X\ESCU\182%U:\243"))))

expected-case-11 : Result
expected-case-11 = success (UCon (tagCon bytestring (mkByteString "\DC3\128\128\DC4\128\128\128\CAN\153\NULB*\STX\136\172\STX\ETXd\NUL\STXT\b0\t\DC4\NUL\SYND\SOH\STX\NUL!\t?!\EOT$\NUL\FS\197P\130\DLE")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-11 : Set
pending-case-11 = Pending (evalRaw test-case-11 ≡ expected-case-11)
```

## case-12

```
-- builtin/semantics/andByteString/case-12
test-case-12 : Untyped
test-case-12 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon bytestring (mkByteString "\219\156\134\FS\152\163\209\156\185(\194*2\170\174\nOt\SOH\DC3\220HsM<\NUL\SYNW\203\143\210\185I\DEL\175\SYN\164\f\RS\205\215\214X\ESCU\182%U:\243"))))

expected-case-12 : Result
expected-case-12 = success (UCon (tagCon bytestring (mkByteString "\DC3\128\128\DC4\128\128\128\CAN\153\NULB*\STX\136\172\STX\ETXd\NUL\STXT\b0\t\DC4\NUL\SYND\SOH\STX\NUL!\t?!\EOT$\NUL\FS\197P\130\DLE\ESCU\182%U:\243")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-12 : Set
pending-case-12 = Pending (evalRaw test-case-12 ≡ expected-case-12)
```

## case-13

```
-- builtin/semantics/andByteString/case-13
test-case-13 : Untyped
test-case-13 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\219\156\134\FS\152\163\209\156\185(\194*2\170\174\nOt\SOH\DC3\220HsM<\NUL\SYNW\203\143\210\185I\DEL\175\SYN\164\f\RS\205\215\214X\ESCU\182%U:\243")))) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176"))))

expected-case-13 : Result
expected-case-13 = success (UCon (tagCon bytestring (mkByteString "\DC3\128\128\DC4\128\128\128\CAN\153\NULB*\STX\136\172\STX\ETXd\NUL\STXT\b0\t\DC4\NUL\SYND\SOH\STX\NUL!\t?!\EOT$\NUL\FS\197P\130\DLE")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-13 : Set
pending-case-13 = Pending (evalRaw test-case-13 ≡ expected-case-13)
```

## case-14

```
-- builtin/semantics/andByteString/case-14
test-case-14 : Untyped
test-case-14 = (UApp (UApp (UApp (UBuiltin andByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "\219\156\134\FS\152\163\209\156\185(\194*2\170\174\nOt\SOH\DC3\220HsM<\NUL\SYNW\203\143\210\185I\DEL\175\SYN\164\f\RS\205\215\214X\ESCU\182%U:\243")))) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176"))))

expected-case-14 : Result
expected-case-14 = success (UCon (tagCon bytestring (mkByteString "\DC3\128\128\DC4\128\128\128\CAN\153\NULB*\STX\136\172\STX\ETXd\NUL\STXT\b0\t\DC4\NUL\SYND\SOH\STX\NUL!\t?!\EOT$\NUL\FS\197P\130\DLE\ESCU\182%U:\243")))

-- Pending: bytestring constant; postulated builtin `andByteString`.
pending-case-14 : Set
pending-case-14 = Pending (evalRaw test-case-14 ≡ expected-case-14)
```
