---
title: Conformance.Example
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/example`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Example where

open import Conformance.Eval
```

## ApplyAdd1

```
-- example/ApplyAdd1
test-ApplyAdd1 : Untyped
test-ApplyAdd1 = (UApp (UApp (UForce (UForce (UDelay (UDelay (ULambda (ULambda (UApp (UVar 1) (UVar 0)))))))) (UApp (UBuiltin addInteger) (UApp (ULambda (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UBuiltin multiplyInteger) (UVar 0)) (UVar 0))) (UApp (UApp (UBuiltin subtractInteger) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 1))))) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 3)))) (UCon (tagCon integer (ℤ.pos 0))))))) (UApp (ULambda (UApp (UApp (UBuiltin subtractInteger) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 2))))) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 1)))))) (UApp (ULambda (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 2))))) (UApp (UBuiltin sha3-256) (UCon (tagCon bytestring (mkByteString "v"))))))))) (UApp (ULambda (UApp (UApp (UBuiltin addInteger) (UApp (UApp (UBuiltin addInteger) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 1))))) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 3)))))) (UApp (UApp (UBuiltin subtractInteger) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 2))))) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 1))))))) (UApp (UApp (UBuiltin lessThanInteger) (UCon (tagCon integer (ℤ.pos 3)))) (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 1))))) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 0))))))))

expected-ApplyAdd1 : Result
expected-ApplyAdd1 = success (UCon (tagCon integer (ℤ.pos 1)))

-- Pending: bytestring constant; postulated builtin `sha3-256`.
pending-ApplyAdd1 : Set
pending-ApplyAdd1 = Pending (evalRaw test-ApplyAdd1 ≡ expected-ApplyAdd1)
```

## ApplyAdd2

```
-- example/ApplyAdd2
test-ApplyAdd2 : Untyped
test-ApplyAdd2 = (UApp (UApp (UApp (UForce (UForce (UDelay (UDelay (ULambda (ULambda (UApp (UVar 1) (UVar 0)))))))) (UBuiltin addInteger)) (UApp (ULambda (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UBuiltin subtractInteger) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 3)))) (UCon (tagCon integer (ℤ.pos 2))))) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 0)))))) (UApp (UApp (UBuiltin subtractInteger) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 3)))) (UCon (tagCon integer (ℤ.pos 0))))) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1))))))) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UApp (UApp (UBuiltin subtractInteger) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 3)))) (UCon (tagCon integer (ℤ.pos 3))))) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 3)))))) (UApp (UApp (UBuiltin addInteger) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 3))))) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 3)))) (UCon (tagCon integer (ℤ.pos 3)))))))) (UApp (ULambda (UApp (ULambda (UApp (UApp (UBuiltin addInteger) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 3))))) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 1)))))) (UApp (UApp (UBuiltin subtractInteger) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1))))) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 0))))))) (UApp (ULambda (UApp (UApp (UBuiltin lessThanInteger) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 3))))) (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 1)))))) (UApp (UApp (UBuiltin equalsInteger) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 3)))) (UCon (tagCon integer (ℤ.pos 2))))) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 0))))))))

expected-ApplyAdd2 : Result
expected-ApplyAdd2 = success (UCon (tagCon integer (ℤ.negsuc 0)))

_ : evalRaw test-ApplyAdd2 ≡ expected-ApplyAdd2
_ = refl
```

## DivideByZero

```
-- example/DivideByZero
test-DivideByZero : Untyped
test-DivideByZero = (UApp (UApp (UBuiltin remainderInteger) (UApp (ULambda (UApp (UApp (UBuiltin addInteger) (UApp (ULambda (UApp (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 3)))) (UCon (tagCon integer (ℤ.pos 3))))) (UApp (UApp (UBuiltin lessThanInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 0)))))) (UApp (ULambda (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 3))))) (UApp (UApp (UBuiltin equalsByteString) (UCon (tagCon bytestring (mkByteString "pc")))) (UCon (tagCon bytestring (mkByteString "qdf"))))))) (UApp (UBuiltin sha2-256) (UApp (UApp (UBuiltin appendByteString) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "gim"))))) (UApp (UBuiltin sha2-256) (UCon (tagCon bytestring (mkByteString "vqt")))))))) (UCon (tagCon integer (ℤ.pos 0))))

expected-DivideByZero : Result
expected-DivideByZero = failure

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `sha2-256`; postulated builtin `appendByteString`.
pending-DivideByZero : Set
pending-DivideByZero = Pending (evalRaw test-DivideByZero ≡ expected-DivideByZero)
```

## DivideByZeroDrop

```
-- example/DivideByZeroDrop
test-DivideByZeroDrop : Untyped
test-DivideByZeroDrop = (UApp (UApp (UForce (UForce (UDelay (UDelay (ULambda (ULambda (UVar 1))))))) (UCon (tagCon integer (ℤ.pos 0)))) (UApp (UApp (UBuiltin divideInteger) (UApp (ULambda (UApp (ULambda (UVar 0)) (UApp (UApp (UBuiltin multiplyInteger) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 0))))) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1))))))) (UApp (ULambda (UCon (tagCon integer (ℤ.pos 1)))) (UApp (UApp (UBuiltin subtractInteger) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 3))))) (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 2)))))))) (UCon (tagCon integer (ℤ.pos 0)))))

expected-DivideByZeroDrop : Result
expected-DivideByZeroDrop = failure

_ : evalRaw test-DivideByZeroDrop ≡ expected-DivideByZeroDrop
_ = refl
```

## IfIntegers

```
-- example/IfIntegers
test-IfIntegers : Untyped
test-IfIntegers = (UApp (UApp (UApp (UForce (UDelay (ULambda (ULambda (ULambda (UApp (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UVar 2)) (UVar 1)) (UVar 0)) (UCon (tagCon unit tt)))))))) (UApp (ULambda (UApp (UApp (UBuiltin equalsByteString) (UApp (UBuiltin sha2-256) (UApp (UBuiltin sha3-256) (UCon (tagCon bytestring (mkByteString "d")))))) (UVar 0))) (UApp (UApp (UBuiltin appendByteString) (UApp (ULambda (UApp (UBuiltin sha3-256) (UCon (tagCon bytestring (mkByteString "x"))))) (UApp (UBuiltin sha3-256) (UCon (tagCon bytestring (mkByteString "rn")))))) (UCon (tagCon bytestring (mkByteString "is")))))) (UApp (UForce (UForce (UDelay (UDelay (ULambda (ULambda (UVar 1))))))) (UApp (ULambda (UApp (ULambda (UVar 1)) (UApp (UBuiltin sha2-256) (UApp (UBuiltin sha3-256) (UCon (tagCon bytestring (mkByteString ""))))))) (UApp (UApp (UBuiltin subtractInteger) (UApp (UApp (UBuiltin addInteger) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 2)))) (UCon (tagCon integer (ℤ.pos 2))))) (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 3)))))) (UApp (ULambda (UApp (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 3)))) (UCon (tagCon integer (ℤ.pos 3))))) (UApp (UApp (UBuiltin equalsByteString) (UCon (tagCon bytestring (mkByteString "lz")))) (UCon (tagCon bytestring (mkByteString "fs"))))))))) (UApp (UForce (UForce (UDelay (UDelay (ULambda (ULambda (UVar 1))))))) (UCon (tagCon integer (ℤ.pos 0)))))

expected-IfIntegers : Result
expected-IfIntegers = success (UCon (tagCon integer (ℤ.pos 0)))

-- Pending: bytestring constant; postulated builtin `equalsByteString`; postulated builtin `sha2-256`; postulated builtin `sha3-256`; postulated builtin `appendByteString`.
pending-IfIntegers : Set
pending-IfIntegers = Pending (evalRaw test-IfIntegers ≡ expected-IfIntegers)
```

## NatRoundTrip

```
-- example/NatRoundTrip
test-NatRoundTrip : Untyped
test-NatRoundTrip = (UApp (UApp (UApp (UForce (UDelay (ULambda (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (ULambda (ULambda (UApp (UApp (UVar 2) (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (UVar 1))) (UVar 0)))))))))) (ULambda (ULambda (ULambda (UApp (UApp (UForce (UVar 0)) (UVar 1)) (ULambda (UApp (UApp (UVar 3) (UApp (UVar 4) (UVar 2))) (UVar 0))))))))))) (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 1))))) (UCon (tagCon integer (ℤ.pos 0)))) (UApp (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UVar 2)))))) (UDelay (ULambda (ULambda (UVar 1))))))

expected-NatRoundTrip : Result
expected-NatRoundTrip = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-NatRoundTrip ≡ expected-NatRoundTrip
_ = refl
```

## ScottListSum

```
-- example/ScottListSum
test-ScottListSum : Untyped
test-ScottListSum = (UApp (UApp (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (ULambda (ULambda (UApp (UApp (UVar 2) (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (UVar 1))) (UVar 0)))))))))) (ULambda (ULambda (ULambda (UApp (UApp (UForce (UVar 0)) (UVar 1)) (ULambda (ULambda (UApp (UApp (UVar 4) (UApp (UApp (UVar 5) (UVar 3)) (UVar 1))) (UVar 0)))))))))))))) (UBuiltin addInteger)) (UCon (tagCon integer (ℤ.pos 0)))) (UForce (UDelay (UDelay (ULambda (ULambda (UVar 1)))))))

expected-ScottListSum : Result
expected-ScottListSum = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-ScottListSum ≡ expected-ScottListSum
_ = refl
```

## churchSucc

```
-- example/churchSucc
test-churchSucc : Untyped
test-churchSucc = (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UApp (UApp (UForce (UVar 2)) (UVar 1)) (UVar 0)))))))

expected-churchSucc : Result
expected-churchSucc = success (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UApp (UApp (UForce (UVar 2)) (UVar 1)) (UVar 0)))))))

_ : evalRaw test-churchSucc ≡ expected-churchSucc
_ = refl
```

## churchZero

```
-- example/churchZero
test-churchZero : Untyped
test-churchZero = (UDelay (ULambda (ULambda (UVar 1))))

expected-churchZero : Result
expected-churchZero = success (UDelay (ULambda (ULambda (UVar 1))))

_ : evalRaw test-churchZero ≡ expected-churchZero
_ = refl
```

## even2

```
-- example/even2
test-even2 : Untyped
test-even2 = (UApp (UApp (UForce (UApp (UForce (UForce (UForce (UForce (UDelay (UDelay (UDelay (UDelay (ULambda (UApp (UApp (UForce (UDelay (ULambda (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (ULambda (ULambda (UApp (UApp (UVar 2) (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (UVar 1))) (UVar 0)))))))))) (ULambda (ULambda (UDelay (ULambda (UApp (UForce (UApp (UVar 3) (UDelay (ULambda (UApp (UForce (UApp (UVar 3) (UVar 2))) (UApp (UForce (UVar 2)) (UVar 0))))))) (UVar 0)))))))))) (ULambda (UDelay (ULambda (UApp (UApp (UVar 0) (ULambda (UApp (UForce (UVar 2)) (ULambda (ULambda (UApp (UVar 1) (UVar 2))))))) (ULambda (UApp (UForce (UVar 2)) (ULambda (ULambda (UApp (UVar 0) (UVar 2))))))))))) (UVar 0))))))))))) (UDelay (ULambda (ULambda (ULambda (UApp (UApp (UVar 2) (ULambda (UApp (UApp (UForce (UVar 0)) (UCon (tagCon bool true))) (UVar 1)))) (ULambda (UApp (UApp (UForce (UVar 0)) (UCon (tagCon bool false))) (UVar 2)))))))))) (ULambda (ULambda (UVar 1)))) (UApp (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UVar 2)))))) (UApp (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UVar 2)))))) (UDelay (ULambda (ULambda (UVar 1)))))))

expected-even2 : Result
expected-even2 = success (UCon (tagCon bool true))

_ : evalRaw test-even2 ≡ expected-even2
_ = refl
```

## even3

```
-- example/even3
test-even3 : Untyped
test-even3 = (UApp (UApp (UForce (UApp (UForce (UForce (UForce (UForce (UDelay (UDelay (UDelay (UDelay (ULambda (UApp (UApp (UForce (UDelay (ULambda (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (ULambda (ULambda (UApp (UApp (UVar 2) (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (UVar 1))) (UVar 0)))))))))) (ULambda (ULambda (UDelay (ULambda (UApp (UForce (UApp (UVar 3) (UDelay (ULambda (UApp (UForce (UApp (UVar 3) (UVar 2))) (UApp (UForce (UVar 2)) (UVar 0))))))) (UVar 0)))))))))) (ULambda (UDelay (ULambda (UApp (UApp (UVar 0) (ULambda (UApp (UForce (UVar 2)) (ULambda (ULambda (UApp (UVar 1) (UVar 2))))))) (ULambda (UApp (UForce (UVar 2)) (ULambda (ULambda (UApp (UVar 0) (UVar 2))))))))))) (UVar 0))))))))))) (UDelay (ULambda (ULambda (ULambda (UApp (UApp (UVar 2) (ULambda (UApp (UApp (UForce (UVar 0)) (UCon (tagCon bool true))) (UVar 1)))) (ULambda (UApp (UApp (UForce (UVar 0)) (UCon (tagCon bool false))) (UVar 2)))))))))) (ULambda (ULambda (UVar 1)))) (UApp (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UVar 2)))))) (UApp (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UVar 2)))))) (UApp (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UVar 2)))))) (UDelay (ULambda (ULambda (UVar 1))))))))

expected-even3 : Result
expected-even3 = success (UCon (tagCon bool false))

_ : evalRaw test-even3 ≡ expected-even3
_ = refl
```

## evenList

```
-- example/evenList
test-evenList : Untyped
test-evenList = (UApp (UApp (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (ULambda (ULambda (UApp (UApp (UVar 2) (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (UVar 1))) (UVar 0)))))))))) (ULambda (ULambda (ULambda (UApp (UApp (UForce (UVar 0)) (UVar 1)) (ULambda (ULambda (UApp (UApp (UVar 4) (UApp (UApp (UVar 5) (UVar 3)) (UVar 1))) (UVar 0)))))))))))))) (ULambda (ULambda (UApp (UApp (UBuiltin addInteger) (UVar 1)) (UApp (UApp (UApp (UForce (UDelay (ULambda (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (ULambda (ULambda (UApp (UApp (UVar 2) (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (UVar 1))) (UVar 0)))))))))) (ULambda (ULambda (ULambda (UApp (UApp (UForce (UVar 0)) (UVar 1)) (ULambda (UApp (UApp (UVar 3) (UApp (UVar 4) (UVar 2))) (UVar 0))))))))))) (UApp (UBuiltin addInteger) (UCon (tagCon integer (ℤ.pos 1))))) (UCon (tagCon integer (ℤ.pos 0)))) (UVar 0)))))) (UCon (tagCon integer (ℤ.pos 0)))) (UApp (UApp (UForce (UApp (UForce (UForce (UForce (UForce (UDelay (UDelay (UDelay (UDelay (ULambda (UApp (UApp (UForce (UDelay (ULambda (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (ULambda (ULambda (UApp (UApp (UVar 2) (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (UVar 1))) (UVar 0)))))))))) (ULambda (ULambda (UDelay (ULambda (UApp (UForce (UApp (UVar 3) (UDelay (ULambda (UApp (UForce (UApp (UVar 3) (UVar 2))) (UApp (UForce (UVar 2)) (UVar 0))))))) (UVar 0)))))))))) (ULambda (UDelay (ULambda (UApp (UApp (UVar 0) (ULambda (UApp (UForce (UVar 2)) (ULambda (ULambda (UApp (UVar 1) (UVar 2))))))) (ULambda (UApp (UForce (UVar 2)) (ULambda (ULambda (UApp (UVar 0) (UVar 2))))))))))) (UVar 0))))))))))) (UDelay (ULambda (ULambda (ULambda (UApp (UApp (UVar 2) (ULambda (UApp (UApp (UForce (UVar 0)) (UForce (UDelay (UDelay (ULambda (ULambda (UVar 1))))))) (ULambda (ULambda (UApp (UApp (UForce (UDelay (ULambda (ULambda (UDelay (ULambda (ULambda (UApp (UApp (UVar 0) (UVar 3)) (UVar 2))))))))) (UVar 1)) (UApp (UVar 3) (UVar 0)))))))) (ULambda (UApp (UApp (UForce (UVar 0)) (UForce (UDelay (UDelay (ULambda (ULambda (UVar 1))))))) (ULambda (ULambda (UApp (UVar 4) (UVar 0))))))))))))) (ULambda (ULambda (UVar 1)))) (UApp (UApp (UForce (UDelay (ULambda (ULambda (UDelay (ULambda (ULambda (UApp (UApp (UVar 0) (UVar 3)) (UVar 2))))))))) (UApp (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UVar 2)))))) (UDelay (ULambda (ULambda (UVar 1)))))) (UApp (UApp (UForce (UDelay (ULambda (ULambda (UDelay (ULambda (ULambda (UApp (UApp (UVar 0) (UVar 3)) (UVar 2))))))))) (UApp (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UVar 2)))))) (UApp (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UVar 2)))))) (UDelay (ULambda (ULambda (UVar 1))))))) (UApp (UApp (UForce (UDelay (ULambda (ULambda (UDelay (ULambda (ULambda (UApp (UApp (UVar 0) (UVar 3)) (UVar 2))))))))) (UApp (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UVar 2)))))) (UApp (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UVar 2)))))) (UApp (ULambda (UDelay (ULambda (ULambda (UApp (UVar 0) (UVar 2)))))) (UDelay (ULambda (ULambda (UVar 1)))))))) (UForce (UDelay (UDelay (ULambda (ULambda (UVar 1)))))))))))

expected-evenList : Result
expected-evenList = success (UCon (tagCon integer (ℤ.pos 4)))

_ : evalRaw test-evenList ≡ expected-evenList
_ = refl
```

## factorial

```
-- example/factorial
test-factorial : Untyped
test-factorial = (UApp (ULambda (UApp (UApp (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (ULambda (ULambda (UApp (UApp (UVar 2) (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (UVar 1))) (UVar 0)))))))))) (ULambda (ULambda (ULambda (UApp (UApp (UForce (UVar 0)) (UVar 1)) (ULambda (ULambda (UApp (UApp (UVar 4) (UApp (UApp (UVar 5) (UVar 3)) (UVar 1))) (UVar 0)))))))))))))) (UBuiltin multiplyInteger)) (UCon (tagCon integer (ℤ.pos 1)))) (UApp (UApp (ULambda (ULambda (UApp (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (ULambda (ULambda (UApp (UApp (UVar 2) (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (UVar 1))) (UVar 0)))))))))) (ULambda (ULambda (UApp (UApp (UApp (UForce (UDelay (ULambda (ULambda (ULambda (UApp (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UVar 2)) (UVar 1)) (UVar 0)) (UCon (tagCon unit tt)))))))) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UVar 0)) (UVar 2))) (ULambda (UApp (UApp (UForce (UDelay (ULambda (ULambda (UDelay (ULambda (ULambda (UApp (UApp (UVar 0) (UVar 3)) (UVar 2))))))))) (UVar 1)) (UApp (UVar 2) (UApp (ULambda (UApp (UApp (UBuiltin addInteger) (UVar 0)) (UCon (tagCon integer (ℤ.pos 1))))) (UVar 1)))))) (ULambda (UForce (UDelay (UDelay (ULambda (ULambda (UVar 1))))))))))) (UVar 1)))) (UCon (tagCon integer (ℤ.pos 1)))) (UVar 0)))) (UCon (tagCon integer (ℤ.pos 4))))

expected-factorial : Result
expected-factorial = success (UCon (tagCon integer (ℤ.pos 24)))

_ : evalRaw test-factorial ≡ expected-factorial
_ = refl
```

## fibonacci

```
-- example/fibonacci
test-fibonacci : Untyped
test-fibonacci = (UApp (ULambda (UApp (UApp (UForce (UForce (UDelay (UDelay (ULambda (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (ULambda (ULambda (UApp (UApp (UVar 2) (UApp (UForce (UDelay (ULambda (UApp (UVar 0) (UVar 0))))) (UVar 1))) (UVar 0)))))))))) (ULambda (ULambda (UApp (UApp (UApp (UForce (UDelay (ULambda (ULambda (ULambda (UApp (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UVar 2)) (UVar 1)) (UVar 0)) (UCon (tagCon unit tt)))))))) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UVar 0)) (UCon (tagCon integer (ℤ.pos 1))))) (ULambda (UVar 1))) (ULambda (UApp (UApp (UBuiltin addInteger) (UApp (UVar 2) (UApp (UApp (UBuiltin subtractInteger) (UVar 1)) (UCon (tagCon integer (ℤ.pos 1)))))) (UApp (UVar 2) (UApp (UApp (UBuiltin subtractInteger) (UVar 1)) (UCon (tagCon integer (ℤ.pos 2))))))))))) (UVar 0))) (UCon (tagCon integer (ℤ.pos 0))))

expected-fibonacci : Result
expected-fibonacci = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-fibonacci ≡ expected-fibonacci
_ = refl
```

## force-lam

```
-- example/force-lam
test-force-lam : Untyped
test-force-lam = (ULambda (UForce (UVar 0)))

expected-force-lam : Result
expected-force-lam = success (ULambda (UForce (UVar 0)))

_ : evalRaw test-force-lam ≡ expected-force-lam
_ = refl
```

## overapplication

```
-- example/overapplication
test-overapplication : Untyped
test-overapplication = (UApp (UApp (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UApp (UApp (UBuiltin lessThanInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 3))))) (UBuiltin addInteger)) (UBuiltin subtractInteger)) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 3))))

expected-overapplication : Result
expected-overapplication = success (UCon (tagCon integer (ℤ.pos 4)))

_ : evalRaw test-overapplication ≡ expected-overapplication
_ = refl
```

## succInteger

```
-- example/succInteger
test-succInteger : Untyped
test-succInteger = (ULambda (UApp (UApp (UBuiltin addInteger) (UVar 0)) (UCon (tagCon integer (ℤ.pos 1)))))

expected-succInteger : Result
expected-succInteger = success (ULambda (UApp (UApp (UBuiltin addInteger) (UVar 0)) (UCon (tagCon integer (ℤ.pos 1)))))

_ : evalRaw test-succInteger ≡ expected-succInteger
_ = refl
```
