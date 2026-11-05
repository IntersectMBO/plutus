---
title: Conformance.Builtin.Semantics.ComplementByteString
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

<<<<<<< HEAD
_ : evalRaw test-case-01 ≡ expected-case-01
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `complementByteString`.
pending-case-01 : Set
pending-case-01 = Pending (evalRaw test-case-01 ≡ expected-case-01)
>>>>>>> origin/master
```

## case-02

```
-- builtin/semantics/complementByteString/case-02
test-case-02 : Untyped
<<<<<<< HEAD
test-case-02 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString "0f"))))

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon bytestring (mkByteString "f0")))

_ : evalRaw test-case-02 ≡ expected-case-02
_ = refl
=======
test-case-02 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString "\SI"))))

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon bytestring (mkByteString "\240")))

-- Pending: bytestring constant; postulated builtin `complementByteString`.
pending-case-02 : Set
pending-case-02 = Pending (evalRaw test-case-02 ≡ expected-case-02)
>>>>>>> origin/master
```

## case-03

```
-- builtin/semantics/complementByteString/case-03
test-case-03 : Untyped
<<<<<<< HEAD
test-case-03 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString "b00b"))))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon bytestring (mkByteString "4ff4")))

_ : evalRaw test-case-03 ≡ expected-case-03
_ = refl
=======
test-case-03 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString "\176\v"))))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon bytestring (mkByteString "O\244")))

-- Pending: bytestring constant; postulated builtin `complementByteString`.
pending-case-03 : Set
pending-case-03 = Pending (evalRaw test-case-03 ≡ expected-case-03)
>>>>>>> origin/master
```

## case-04

```
-- builtin/semantics/complementByteString/case-04
test-case-04 : Untyped
<<<<<<< HEAD
test-case-04 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString "db9c861c98a3d19cb928c22a32aaae0a4f740113dc48734d3c001657cb8fd2b9497faf16a40c1ecdd7d6581b55b625553af3"))))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon bytestring (mkByteString "246379e3675c2e6346d73dd5cd5551f5b08bfeec23b78cb2c3ffe9a834702d46b68050e95bf3e1322829a7e4aa49daaac50c")))

_ : evalRaw test-case-04 ≡ expected-case-04
_ = refl
=======
test-case-04 = (UApp (UBuiltin complementByteString) (UCon (tagCon bytestring (mkByteString "\219\156\134\FS\152\163\209\156\185(\194*2\170\174\nOt\SOH\DC3\220HsM<\NUL\SYNW\203\143\210\185I\DEL\175\SYN\164\f\RS\205\215\214X\ESCU\182%U:\243"))))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon bytestring (mkByteString "$cy\227g\\.cF\215=\213\205UQ\245\176\139\254\236#\183\140\178\195\255\233\168\&4p-F\182\128P\233[\243\225\&2()\167\228\170I\218\170\197\f")))

-- Pending: bytestring constant; postulated builtin `complementByteString`.
pending-case-04 : Set
pending-case-04 = Pending (evalRaw test-case-04 ≡ expected-case-04)
>>>>>>> origin/master
```

## case-05

```
-- builtin/semantics/complementByteString/case-05
test-case-05 : Untyped
<<<<<<< HEAD
test-case-05 = (UApp (ULambda (UApp (UApp (UBuiltin equalsByteString) (UVar 0)) (UApp (UBuiltin complementByteString) (UApp (UBuiltin complementByteString) (UVar 0))))) (UCon (tagCon bytestring (mkByteString "db9c861c98a3d19cb928c22a32aaae0a4f740113dc48734d3c001657cb8fd2b9497faf16a40c1ecdd7d6581b55b625553af3"))))
=======
test-case-05 = (UApp (ULambda (UApp (UApp (UBuiltin equalsByteString) (UVar 0)) (UApp (UBuiltin complementByteString) (UApp (UBuiltin complementByteString) (UVar 0))))) (UCon (tagCon bytestring (mkByteString "\219\156\134\FS\152\163\209\156\185(\194*2\170\174\nOt\SOH\DC3\220HsM<\NUL\SYNW\203\143\210\185I\DEL\175\SYN\164\f\RS\205\215\214X\ESCU\182%U:\243"))))
>>>>>>> origin/master

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon bool true))

<<<<<<< HEAD
_ : evalRaw test-case-05 ≡ expected-case-05
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `complementByteString`.
pending-case-05 : Set
pending-case-05 = Pending (evalRaw test-case-05 ≡ expected-case-05)
>>>>>>> origin/master
```
