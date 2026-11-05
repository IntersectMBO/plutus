---
title: Conformance.Builtin.Semantics.XorByteString
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
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/xorByteString`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.XorByteString where

open import Conformance.Eval
```

## case-01

```
-- builtin/semantics/xorByteString/case-01
test-case-01 : Untyped
<<<<<<< HEAD
test-case-01 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "ff"))))
=======
test-case-01 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "\255"))))
>>>>>>> origin/master

expected-case-01 : Result
expected-case-01 = success (UCon (tagCon bytestring (mkByteString "")))

<<<<<<< HEAD
_ : evalRaw test-case-01 ≡ expected-case-01
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-01 : Set
pending-case-01 = Pending (evalRaw test-case-01 ≡ expected-case-01)
>>>>>>> origin/master
```

## case-02

```
-- builtin/semantics/xorByteString/case-02
test-case-02 : Untyped
<<<<<<< HEAD
test-case-02 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "ff")))) (UCon (tagCon bytestring (mkByteString ""))))
=======
test-case-02 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon bytestring (mkByteString ""))))
>>>>>>> origin/master

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon bytestring (mkByteString "")))

<<<<<<< HEAD
_ : evalRaw test-case-02 ≡ expected-case-02
_ = refl
=======
-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-02 : Set
pending-case-02 = Pending (evalRaw test-case-02 ≡ expected-case-02)
>>>>>>> origin/master
```

## case-03

```
-- builtin/semantics/xorByteString/case-03
test-case-03 : Untyped
<<<<<<< HEAD
test-case-03 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "ff")))) (UCon (tagCon bytestring (mkByteString "00"))))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon bytestring (mkByteString "ff")))

_ : evalRaw test-case-03 ≡ expected-case-03
_ = refl
=======
test-case-03 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon bytestring (mkByteString "\NUL"))))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon bytestring (mkByteString "\255")))

-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-03 : Set
pending-case-03 = Pending (evalRaw test-case-03 ≡ expected-case-03)
>>>>>>> origin/master
```

## case-04

```
-- builtin/semantics/xorByteString/case-04
test-case-04 : Untyped
<<<<<<< HEAD
test-case-04 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "00")))) (UCon (tagCon bytestring (mkByteString "ff"))))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon bytestring (mkByteString "ff")))

_ : evalRaw test-case-04 ≡ expected-case-04
_ = refl
=======
test-case-04 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon bytestring (mkByteString "\255"))))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon bytestring (mkByteString "\255")))

-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-04 : Set
pending-case-04 = Pending (evalRaw test-case-04 ≡ expected-case-04)
>>>>>>> origin/master
```

## case-05

```
-- builtin/semantics/xorByteString/case-05
test-case-05 : Untyped
<<<<<<< HEAD
test-case-05 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "4f00")))) (UCon (tagCon bytestring (mkByteString "f4"))))

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon bytestring (mkByteString "bb")))

_ : evalRaw test-case-05 ≡ expected-case-05
_ = refl
=======
test-case-05 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "O\NUL")))) (UCon (tagCon bytestring (mkByteString "\244"))))

expected-case-05 : Result
expected-case-05 = success (UCon (tagCon bytestring (mkByteString "\187")))

-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-05 : Set
pending-case-05 = Pending (evalRaw test-case-05 ≡ expected-case-05)
>>>>>>> origin/master
```

## case-06

```
-- builtin/semantics/xorByteString/case-06
test-case-06 : Untyped
<<<<<<< HEAD
test-case-06 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "ff"))))

expected-case-06 : Result
expected-case-06 = success (UCon (tagCon bytestring (mkByteString "ff")))

_ : evalRaw test-case-06 ≡ expected-case-06
_ = refl
=======
test-case-06 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "")))) (UCon (tagCon bytestring (mkByteString "\255"))))

expected-case-06 : Result
expected-case-06 = success (UCon (tagCon bytestring (mkByteString "\255")))

-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-06 : Set
pending-case-06 = Pending (evalRaw test-case-06 ≡ expected-case-06)
>>>>>>> origin/master
```

## case-07

```
-- builtin/semantics/xorByteString/case-07
test-case-07 : Untyped
<<<<<<< HEAD
test-case-07 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "ff")))) (UCon (tagCon bytestring (mkByteString ""))))

expected-case-07 : Result
expected-case-07 = success (UCon (tagCon bytestring (mkByteString "ff")))

_ : evalRaw test-case-07 ≡ expected-case-07
_ = refl
=======
test-case-07 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon bytestring (mkByteString ""))))

expected-case-07 : Result
expected-case-07 = success (UCon (tagCon bytestring (mkByteString "\255")))

-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-07 : Set
pending-case-07 = Pending (evalRaw test-case-07 ≡ expected-case-07)
>>>>>>> origin/master
```

## case-08

```
-- builtin/semantics/xorByteString/case-08
test-case-08 : Untyped
<<<<<<< HEAD
test-case-08 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "ff")))) (UCon (tagCon bytestring (mkByteString "00"))))

expected-case-08 : Result
expected-case-08 = success (UCon (tagCon bytestring (mkByteString "ff")))

_ : evalRaw test-case-08 ≡ expected-case-08
_ = refl
=======
test-case-08 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "\255")))) (UCon (tagCon bytestring (mkByteString "\NUL"))))

expected-case-08 : Result
expected-case-08 = success (UCon (tagCon bytestring (mkByteString "\255")))

-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-08 : Set
pending-case-08 = Pending (evalRaw test-case-08 ≡ expected-case-08)
>>>>>>> origin/master
```

## case-09

```
-- builtin/semantics/xorByteString/case-09
test-case-09 : Untyped
<<<<<<< HEAD
test-case-09 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "00")))) (UCon (tagCon bytestring (mkByteString "ff"))))

expected-case-09 : Result
expected-case-09 = success (UCon (tagCon bytestring (mkByteString "ff")))

_ : evalRaw test-case-09 ≡ expected-case-09
_ = refl
=======
test-case-09 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "\NUL")))) (UCon (tagCon bytestring (mkByteString "\255"))))

expected-case-09 : Result
expected-case-09 = success (UCon (tagCon bytestring (mkByteString "\255")))

-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-09 : Set
pending-case-09 = Pending (evalRaw test-case-09 ≡ expected-case-09)
>>>>>>> origin/master
```

## case-10

```
-- builtin/semantics/xorByteString/case-10
test-case-10 : Untyped
<<<<<<< HEAD
test-case-10 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "4f00")))) (UCon (tagCon bytestring (mkByteString "f4"))))

expected-case-10 : Result
expected-case-10 = success (UCon (tagCon bytestring (mkByteString "bb00")))

_ : evalRaw test-case-10 ≡ expected-case-10
_ = refl
=======
test-case-10 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "O\NUL")))) (UCon (tagCon bytestring (mkByteString "\244"))))

expected-case-10 : Result
expected-case-10 = success (UCon (tagCon bytestring (mkByteString "\187\NUL")))

-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-10 : Set
pending-case-10 = Pending (evalRaw test-case-10 ≡ expected-case-10)
>>>>>>> origin/master
```

## case-11

```
-- builtin/semantics/xorByteString/case-11
test-case-11 : Untyped
<<<<<<< HEAD
test-case-11 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon bytestring (mkByteString "db9c861c98a3d19cb928c22a32aaae0a4f740113dc48734d3c001657cb8fd2b9497faf16a40c1ecdd7d6581b55b625553af3"))))

expected-case-11 : Result
expected-case-11 = success (UCon (tagCon bytestring (mkByteString "e85e76ca1d2751a724e899113936136ccc99c1dda863c3d46b612813de8dd7ded440ceb2c3be420a8f75e8")))

_ : evalRaw test-case-11 ≡ expected-case-11
_ = refl
=======
test-case-11 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon bytestring (mkByteString "\219\156\134\FS\152\163\209\156\185(\194*2\170\174\nOt\SOH\DC3\220HsM<\NUL\SYNW\203\143\210\185I\DEL\175\SYN\164\f\RS\205\215\214X\ESCU\182%U:\243"))))

expected-case-11 : Result
expected-case-11 = success (UCon (tagCon bytestring (mkByteString "\232^v\202\GS'Q\167$\232\153\DC196\DC3l\204\153\193\221\168c\195\212ka(\DC3\222\141\215\222\212@\206\178\195\190B\n\143u\232")))

-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-11 : Set
pending-case-11 = Pending (evalRaw test-case-11 ≡ expected-case-11)
>>>>>>> origin/master
```

## case-12

```
-- builtin/semantics/xorByteString/case-12
test-case-12 : Untyped
<<<<<<< HEAD
test-case-12 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0")))) (UCon (tagCon bytestring (mkByteString "db9c861c98a3d19cb928c22a32aaae0a4f740113dc48734d3c001657cb8fd2b9497faf16a40c1ecdd7d6581b55b625553af3"))))

expected-case-12 : Result
expected-case-12 = success (UCon (tagCon bytestring (mkByteString "e85e76ca1d2751a724e899113936136ccc99c1dda863c3d46b612813de8dd7ded440ceb2c3be420a8f75e81b55b625553af3")))

_ : evalRaw test-case-12 ≡ expected-case-12
_ = refl
=======
test-case-12 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176")))) (UCon (tagCon bytestring (mkByteString "\219\156\134\FS\152\163\209\156\185(\194*2\170\174\nOt\SOH\DC3\220HsM<\NUL\SYNW\203\143\210\185I\DEL\175\SYN\164\f\RS\205\215\214X\ESCU\182%U:\243"))))

expected-case-12 : Result
expected-case-12 = success (UCon (tagCon bytestring (mkByteString "\232^v\202\GS'Q\167$\232\153\DC196\DC3l\204\153\193\221\168c\195\212ka(\DC3\222\141\215\222\212@\206\178\195\190B\n\143u\232\ESCU\182%U:\243")))

-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-12 : Set
pending-case-12 = Pending (evalRaw test-case-12 ≡ expected-case-12)
>>>>>>> origin/master
```

## case-13

```
-- builtin/semantics/xorByteString/case-13
test-case-13 : Untyped
<<<<<<< HEAD
test-case-13 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "db9c861c98a3d19cb928c22a32aaae0a4f740113dc48734d3c001657cb8fd2b9497faf16a40c1ecdd7d6581b55b625553af3")))) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0"))))

expected-case-13 : Result
expected-case-13 = success (UCon (tagCon bytestring (mkByteString "e85e76ca1d2751a724e899113936136ccc99c1dda863c3d46b612813de8dd7ded440ceb2c3be420a8f75e8")))

_ : evalRaw test-case-13 ≡ expected-case-13
_ = refl
=======
test-case-13 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool false))) (UCon (tagCon bytestring (mkByteString "\219\156\134\FS\152\163\209\156\185(\194*2\170\174\nOt\SOH\DC3\220HsM<\NUL\SYNW\203\143\210\185I\DEL\175\SYN\164\f\RS\205\215\214X\ESCU\182%U:\243")))) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176"))))

expected-case-13 : Result
expected-case-13 = success (UCon (tagCon bytestring (mkByteString "\232^v\202\GS'Q\167$\232\153\DC196\DC3l\204\153\193\221\168c\195\212ka(\DC3\222\141\215\222\212@\206\178\195\190B\n\143u\232")))

-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-13 : Set
pending-case-13 = Pending (evalRaw test-case-13 ≡ expected-case-13)
>>>>>>> origin/master
```

## case-14

```
-- builtin/semantics/xorByteString/case-14
test-case-14 : Untyped
<<<<<<< HEAD
test-case-14 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "db9c861c98a3d19cb928c22a32aaae0a4f740113dc48734d3c001657cb8fd2b9497faf16a40c1ecdd7d6581b55b625553af3")))) (UCon (tagCon bytestring (mkByteString "33c2f0d68584803b9dc05b3b0b9cbd6683edc0ce742bb09957613e44150205679d3f61a467b25cc758a3b0"))))

expected-case-14 : Result
expected-case-14 = success (UCon (tagCon bytestring (mkByteString "e85e76ca1d2751a724e899113936136ccc99c1dda863c3d46b612813de8dd7ded440ceb2c3be420a8f75e81b55b625553af3")))

_ : evalRaw test-case-14 ≡ expected-case-14
_ = refl
=======
test-case-14 = (UApp (UApp (UApp (UBuiltin xorByteString) (UCon (tagCon bool true))) (UCon (tagCon bytestring (mkByteString "\219\156\134\FS\152\163\209\156\185(\194*2\170\174\nOt\SOH\DC3\220HsM<\NUL\SYNW\203\143\210\185I\DEL\175\SYN\164\f\RS\205\215\214X\ESCU\182%U:\243")))) (UCon (tagCon bytestring (mkByteString "3\194\240\214\133\132\128;\157\192[;\v\156\189f\131\237\192\206t+\176\153Wa>D\NAK\STX\ENQg\157?a\164g\178\\\199X\163\176"))))

expected-case-14 : Result
expected-case-14 = success (UCon (tagCon bytestring (mkByteString "\232^v\202\GS'Q\167$\232\153\DC196\DC3l\204\153\193\221\168c\195\212ka(\DC3\222\141\215\222\212@\206\178\195\190B\n\143u\232\ESCU\182%U:\243")))

-- Pending: bytestring constant; postulated builtin `xorByteString`.
pending-case-14 : Set
pending-case-14 = Pending (evalRaw test-case-14 ≡ expected-case-14)
>>>>>>> origin/master
```
