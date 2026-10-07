---
title: Conformance.Builtin.Interleaving
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/interleaving`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Interleaving where

open import Conformance.Eval
```

## ite

```
-- builtin/interleaving/ite
test-ite : Untyped
test-ite = (UBuiltin ifThenElse)

expected-ite : Result
expected-ite = success (UBuiltin ifThenElse)

_ : evalRaw test-ite ≡ expected-ite
_ = refl
```

## iteAtIntegerArrowIntegerApplied1

```
-- builtin/interleaving/iteAtIntegerArrowIntegerApplied1
test-iteAtIntegerArrowIntegerApplied1 : Untyped
test-iteAtIntegerArrowIntegerApplied1 = (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.pos 22))))) (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 11))))) (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 22)))))

expected-iteAtIntegerArrowIntegerApplied1 : Result
expected-iteAtIntegerArrowIntegerApplied1 = success (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 11))))

_ : evalRaw test-iteAtIntegerArrowIntegerApplied1 ≡ expected-iteAtIntegerArrowIntegerApplied1
_ = refl
```

## iteAtIntegerArrowIntegerApplied2

```
-- builtin/interleaving/iteAtIntegerArrowIntegerApplied2
test-iteAtIntegerArrowIntegerApplied2 : Untyped
test-iteAtIntegerArrowIntegerApplied2 = (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.pos 22))))) (UBuiltin multiplyInteger)) (UBuiltin subtractInteger))

expected-iteAtIntegerArrowIntegerApplied2 : Result
expected-iteAtIntegerArrowIntegerApplied2 = success (UBuiltin multiplyInteger)

_ : evalRaw test-iteAtIntegerArrowIntegerApplied2 ≡ expected-iteAtIntegerArrowIntegerApplied2
_ = refl
```

## iteAtIntegerArrowIntegerAppliedApplied

```
-- builtin/interleaving/iteAtIntegerArrowIntegerAppliedApplied
test-iteAtIntegerArrowIntegerAppliedApplied : Untyped
test-iteAtIntegerArrowIntegerAppliedApplied = (UApp (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.pos 22))))) (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 11))))) (UApp (UBuiltin subtractInteger) (UCon (tagCon integer (ℤ.pos 22))))) (UCon (tagCon integer (ℤ.pos 22))))

expected-iteAtIntegerArrowIntegerAppliedApplied : Result
expected-iteAtIntegerArrowIntegerAppliedApplied = success (UCon (tagCon integer (ℤ.pos 242)))

_ : evalRaw test-iteAtIntegerArrowIntegerAppliedApplied ≡ expected-iteAtIntegerArrowIntegerAppliedApplied
_ = refl
```

## iteAtIntegerArrowIntegerWithCond

```
-- builtin/interleaving/iteAtIntegerArrowIntegerWithCond
test-iteAtIntegerArrowIntegerWithCond : Untyped
test-iteAtIntegerArrowIntegerWithCond = (UApp (UForce (UBuiltin ifThenElse)) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.pos 22)))))

expected-iteAtIntegerArrowIntegerWithCond : Result
expected-iteAtIntegerArrowIntegerWithCond = success (UApp (UForce (UBuiltin ifThenElse)) (UCon (tagCon bool true)))

_ : evalRaw test-iteAtIntegerArrowIntegerWithCond ≡ expected-iteAtIntegerArrowIntegerWithCond
_ = refl
```

## iteForceAppForce

```
-- builtin/interleaving/iteForceAppForce
test-iteForceAppForce : Untyped
test-iteForceAppForce = (UForce (UApp (UForce (UBuiltin ifThenElse)) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.pos 22))))))

expected-iteForceAppForce : Result
expected-iteForceAppForce = failure

_ : evalRaw test-iteForceAppForce ≡ expected-iteForceAppForce
_ = refl
```

## iteForced

```
-- builtin/interleaving/iteForced
test-iteForced : Untyped
test-iteForced = (UForce (UBuiltin ifThenElse))

expected-iteForced : Result
expected-iteForced = success (UForce (UBuiltin ifThenElse))

_ : evalRaw test-iteForced ≡ expected-iteForced
_ = refl
```

## iteForcedForced

```
-- builtin/interleaving/iteForcedForced
test-iteForcedForced : Untyped
test-iteForcedForced = (UForce (UForce (UBuiltin ifThenElse)))

expected-iteForcedForced : Result
expected-iteForcedForced = failure

_ : evalRaw test-iteForcedForced ≡ expected-iteForcedForced
_ = refl
```

## iteForcedWithIntegerAndString

```
-- builtin/interleaving/iteForcedWithIntegerAndString
test-iteForcedWithIntegerAndString : Untyped
test-iteForcedWithIntegerAndString = (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.pos 22))))) (UCon (tagCon integer (ℤ.pos 33)))) (UCon (tagCon string "abc")))

expected-iteForcedWithIntegerAndString : Result
expected-iteForcedWithIntegerAndString = success (UCon (tagCon integer (ℤ.pos 33)))

_ : evalRaw test-iteForcedWithIntegerAndString ≡ expected-iteForcedWithIntegerAndString
_ = refl
```

## iteStringInteger

```
-- builtin/interleaving/iteStringInteger
-- This is OK because the branches are terms and there's no requirement that
--their types match in UPLC even if they do happen to be builtin constants.
test-iteStringInteger : Untyped
test-iteStringInteger = (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.pos 22))))) (UCon (tagCon string "11 <= 22"))) (UCon (tagCon integer (ℤ.negsuc 1110))))

expected-iteStringInteger : Result
expected-iteStringInteger = success (UCon (tagCon string "11 <= 22"))

_ : evalRaw test-iteStringInteger ≡ expected-iteStringInteger
_ = refl
```

## iteStringString

```
-- builtin/interleaving/iteStringString
test-iteStringString : Untyped
test-iteStringString = (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.pos 22))))) (UCon (tagCon string "11 <= 22"))) (UCon (tagCon string "\172(11 <= 22)")))

expected-iteStringString : Result
expected-iteStringString = success (UCon (tagCon string "11 <= 22"))

_ : evalRaw test-iteStringString ≡ expected-iteStringString
_ = refl
```

## iteUnforcedFullyApplied

```
-- builtin/interleaving/iteUnforcedFullyApplied
test-iteUnforcedFullyApplied : Untyped
test-iteUnforcedFullyApplied = (UApp (UApp (UApp (UBuiltin ifThenElse) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.pos 22))))) (UCon (tagCon string "11 <= 22"))) (UCon (tagCon string "\172(11 <= 22)")))

expected-iteUnforcedFullyApplied : Result
expected-iteUnforcedFullyApplied = failure

_ : evalRaw test-iteUnforcedFullyApplied ≡ expected-iteUnforcedFullyApplied
_ = refl
```

## iteUnforcedWithCond

```
-- builtin/interleaving/iteUnforcedWithCond
test-iteUnforcedWithCond : Untyped
test-iteUnforcedWithCond = (UApp (UBuiltin ifThenElse) (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.pos 22)))))

expected-iteUnforcedWithCond : Result
expected-iteUnforcedWithCond = failure

_ : evalRaw test-iteUnforcedWithCond ≡ expected-iteUnforcedWithCond
_ = refl
```

## iteWrongCondTypeFullyAppied

```
-- builtin/interleaving/iteWrongCondTypeFullyAppied
test-iteWrongCondTypeFullyAppied : Untyped
test-iteWrongCondTypeFullyAppied = (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UCon (tagCon string "11 <= 22"))) (UCon (tagCon string "\172(11 <= 22)"))) (UCon (tagCon string "\172(11 <= 22)")))

expected-iteWrongCondTypeFullyAppied : Result
expected-iteWrongCondTypeFullyAppied = failure

_ : evalRaw test-iteWrongCondTypeFullyAppied ≡ expected-iteWrongCondTypeFullyAppied
_ = refl
```

## iteWrongCondTypePartiallyApplied

```
-- builtin/interleaving/iteWrongCondTypePartiallyApplied
test-iteWrongCondTypePartiallyApplied : Untyped
test-iteWrongCondTypePartiallyApplied = (UApp (UApp (UForce (UBuiltin ifThenElse)) (UCon (tagCon string "11 <= 22"))) (UCon (tagCon string "\172(11 <= 22)")))

expected-iteWrongCondTypePartiallyApplied : Result
expected-iteWrongCondTypePartiallyApplied = success (UApp (UApp (UForce (UBuiltin ifThenElse)) (UCon (tagCon string "11 <= 22"))) (UCon (tagCon string "\172(11 <= 22)")))

_ : evalRaw test-iteWrongCondTypePartiallyApplied ≡ expected-iteWrongCondTypePartiallyApplied
_ = refl
```

## multiplyIntegerForceError1

```
-- builtin/interleaving/multiplyIntegerForceError1
test-multiplyIntegerForceError1 : Untyped
test-multiplyIntegerForceError1 = (UApp (UApp (UForce (UBuiltin multiplyInteger)) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.pos 22))))

expected-multiplyIntegerForceError1 : Result
expected-multiplyIntegerForceError1 = failure

_ : evalRaw test-multiplyIntegerForceError1 ≡ expected-multiplyIntegerForceError1
_ = refl
```

## multiplyIntegerForceError2

```
-- builtin/interleaving/multiplyIntegerForceError2
test-multiplyIntegerForceError2 : Untyped
test-multiplyIntegerForceError2 = (UApp (UForce (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 11))))) (UCon (tagCon integer (ℤ.pos 22))))

expected-multiplyIntegerForceError2 : Result
expected-multiplyIntegerForceError2 = failure

_ : evalRaw test-multiplyIntegerForceError2 ≡ expected-multiplyIntegerForceError2
_ = refl
```

## multiplyIntegerForceError3

```
-- builtin/interleaving/multiplyIntegerForceError3
test-multiplyIntegerForceError3 : Untyped
test-multiplyIntegerForceError3 = (UForce (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.pos 22)))))

expected-multiplyIntegerForceError3 : Result
expected-multiplyIntegerForceError3 = failure

_ : evalRaw test-multiplyIntegerForceError3 ≡ expected-multiplyIntegerForceError3
_ = refl
```
