---
title: Conformance.Builtin.Semantics.IfThenElse
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/ifThenElse`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.IfThenElse where

open import Conformance.Eval
```

## ifThenElse-01

```
-- builtin/semantics/ifThenElse/ifThenElse-01
test-ifThenElse-01 : Untyped
test-ifThenElse-01 = (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UCon (tagCon bool true))) (ULambda (UVar 0))) (UCon (tagCon integer (ℤ.pos 2))))

expected-ifThenElse-01 : Result
expected-ifThenElse-01 = success (ULambda (UVar 0))

_ : evalRaw test-ifThenElse-01 ≡ expected-ifThenElse-01
_ = refl
```

## ifThenElse-02

```
-- builtin/semantics/ifThenElse/ifThenElse-02
test-ifThenElse-02 : Untyped
test-ifThenElse-02 = (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UCon (tagCon bool false))) (ULambda (UVar 0))) (ULambda (ULambda (UVar 0))))

expected-ifThenElse-02 : Result
expected-ifThenElse-02 = success (ULambda (ULambda (UVar 0)))

_ : evalRaw test-ifThenElse-02 ≡ expected-ifThenElse-02
_ = refl
```

## ifThenElse-03

```
-- builtin/semantics/ifThenElse/ifThenElse-03
test-ifThenElse-03 : Untyped
test-ifThenElse-03 = (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UCon (tagCon bool false))) (ULambda (UVar 0))) (UCon (tagCon integer (ℤ.pos 42))))

expected-ifThenElse-03 : Result
expected-ifThenElse-03 = success (UCon (tagCon integer (ℤ.pos 42)))

_ : evalRaw test-ifThenElse-03 ≡ expected-ifThenElse-03
_ = refl
```

## ifThenElse-04

```
-- builtin/semantics/ifThenElse/ifThenElse-04
test-ifThenElse-04 : Untyped
test-ifThenElse-04 = (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UCon (tagCon bool false))) UError) (UCon (tagCon integer (ℤ.pos 42))))

expected-ifThenElse-04 : Result
expected-ifThenElse-04 = failure

_ : evalRaw test-ifThenElse-04 ≡ expected-ifThenElse-04
_ = refl
```

## ifThenElse-bad-cond-01

```
-- builtin/semantics/ifThenElse/ifThenElse-bad-cond-01
test-ifThenElse-bad-cond-01 : Untyped
test-ifThenElse-bad-cond-01 = (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.negsuc 21))))

expected-ifThenElse-bad-cond-01 : Result
expected-ifThenElse-bad-cond-01 = failure

_ : evalRaw test-ifThenElse-bad-cond-01 ≡ expected-ifThenElse-bad-cond-01
_ = refl
```

## ifThenElse-bad-cond-02

```
-- builtin/semantics/ifThenElse/ifThenElse-bad-cond-02
test-ifThenElse-bad-cond-02 : Untyped
test-ifThenElse-bad-cond-02 = (UApp (UApp (UApp (UForce (UBuiltin ifThenElse)) (ULambda (ULambda (UVar 1)))) (UCon (tagCon integer (ℤ.pos 11)))) (UCon (tagCon integer (ℤ.negsuc 21))))

expected-ifThenElse-bad-cond-02 : Result
expected-ifThenElse-bad-cond-02 = failure

_ : evalRaw test-ifThenElse-bad-cond-02 ≡ expected-ifThenElse-bad-cond-02
_ = refl
```

## ifThenElse-no-force

```
-- builtin/semantics/ifThenElse/ifThenElse-no-force
test-ifThenElse-no-force : Untyped
test-ifThenElse-no-force = (UApp (UApp (UApp (UBuiltin ifThenElse) (UCon (tagCon bool true))) (UCon (tagCon integer (ℤ.pos 0)))) (UCon (tagCon integer (ℤ.pos 1))))

expected-ifThenElse-no-force : Result
expected-ifThenElse-no-force = failure

_ : evalRaw test-ifThenElse-no-force ≡ expected-ifThenElse-no-force
_ = refl
```
