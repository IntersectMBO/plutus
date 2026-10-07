---
title: Conformance.Builtin.Semantics.MultiplyInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/multiplyInteger`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.MultiplyInteger where

open import Conformance.Eval
```

## multiplyInteger-01

```
-- builtin/semantics/multiplyInteger/multiplyInteger-01
test-multiplyInteger-01 : Untyped
test-multiplyInteger-01 = (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 1))))

expected-multiplyInteger-01 : Result
expected-multiplyInteger-01 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-multiplyInteger-01 ≡ expected-multiplyInteger-01
_ = refl
```

## multiplyInteger-02

```
-- builtin/semantics/multiplyInteger/multiplyInteger-02
test-multiplyInteger-02 : Untyped
test-multiplyInteger-02 = (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 793479793478939166266268485555555)))) (UCon (tagCon integer (ℤ.pos 0))))

expected-multiplyInteger-02 : Result
expected-multiplyInteger-02 = success (UCon (tagCon integer (ℤ.pos 0)))

_ : evalRaw test-multiplyInteger-02 ≡ expected-multiplyInteger-02
_ = refl
```

## multiplyInteger-03

```
-- builtin/semantics/multiplyInteger/multiplyInteger-03
test-multiplyInteger-03 : Untyped
test-multiplyInteger-03 = (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 793479793478939)))) (UCon (tagCon integer (ℤ.pos 166266268485555555))))

expected-multiplyInteger-03 : Result
expected-multiplyInteger-03 = success (UCon (tagCon integer (ℤ.pos 131928924380432445633603606956145)))

_ : evalRaw test-multiplyInteger-03 ≡ expected-multiplyInteger-03
_ = refl
```

## multiplyInteger-04

```
-- builtin/semantics/multiplyInteger/multiplyInteger-04
test-multiplyInteger-04 : Untyped
test-multiplyInteger-04 = (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.pos 793479793478939)))) (UCon (tagCon integer (ℤ.negsuc 166266268485555554))))

expected-multiplyInteger-04 : Result
expected-multiplyInteger-04 = success (UCon (tagCon integer (ℤ.negsuc 131928924380432445633603606956144)))

_ : evalRaw test-multiplyInteger-04 ≡ expected-multiplyInteger-04
_ = refl
```

## multiplyInteger-05

```
-- builtin/semantics/multiplyInteger/multiplyInteger-05
test-multiplyInteger-05 : Untyped
test-multiplyInteger-05 = (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.negsuc 793479793478938)))) (UCon (tagCon integer (ℤ.pos 166266268485555555))))

expected-multiplyInteger-05 : Result
expected-multiplyInteger-05 = success (UCon (tagCon integer (ℤ.negsuc 131928924380432445633603606956144)))

_ : evalRaw test-multiplyInteger-05 ≡ expected-multiplyInteger-05
_ = refl
```

## multiplyInteger-06

```
-- builtin/semantics/multiplyInteger/multiplyInteger-06
test-multiplyInteger-06 : Untyped
test-multiplyInteger-06 = (UApp (UApp (UBuiltin multiplyInteger) (UCon (tagCon integer (ℤ.negsuc 793479793478938)))) (UCon (tagCon integer (ℤ.negsuc 166266268485555554))))

expected-multiplyInteger-06 : Result
expected-multiplyInteger-06 = success (UCon (tagCon integer (ℤ.pos 131928924380432445633603606956145)))

_ : evalRaw test-multiplyInteger-06 ≡ expected-multiplyInteger-06
_ = refl
```
