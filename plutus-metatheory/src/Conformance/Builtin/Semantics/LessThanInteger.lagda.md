---
title: Conformance.Builtin.Semantics.LessThanInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/lessThanInteger`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.LessThanInteger where

open import Conformance.Eval
```

## lessThanInteger-01

```
-- builtin/semantics/lessThanInteger/lessThanInteger-01
test-lessThanInteger-01 : Untyped
test-lessThanInteger-01 = (UApp (UApp (UBuiltin lessThanInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 2))))

expected-lessThanInteger-01 : Result
expected-lessThanInteger-01 = success (UCon (tagCon bool true))

_ : evalRaw test-lessThanInteger-01 ≡ expected-lessThanInteger-01
_ = refl
```

## lessThanInteger-02

```
-- builtin/semantics/lessThanInteger/lessThanInteger-02
test-lessThanInteger-02 : Untyped
test-lessThanInteger-02 = (UApp (UApp (UBuiltin lessThanInteger) (UCon (tagCon integer (ℤ.pos 8)))) (UCon (tagCon integer (ℤ.pos 4))))

expected-lessThanInteger-02 : Result
expected-lessThanInteger-02 = success (UCon (tagCon bool false))

_ : evalRaw test-lessThanInteger-02 ≡ expected-lessThanInteger-02
_ = refl
```

## lessThanInteger-03

```
-- builtin/semantics/lessThanInteger/lessThanInteger-03
test-lessThanInteger-03 : Untyped
test-lessThanInteger-03 = (UApp (UApp (UBuiltin lessThanInteger) (UCon (tagCon integer (ℤ.pos 4)))) (UCon (tagCon integer (ℤ.pos 8))))

expected-lessThanInteger-03 : Result
expected-lessThanInteger-03 = success (UCon (tagCon bool true))

_ : evalRaw test-lessThanInteger-03 ≡ expected-lessThanInteger-03
_ = refl
```

## lessThanInteger-04

```
-- builtin/semantics/lessThanInteger/lessThanInteger-04
test-lessThanInteger-04 : Untyped
test-lessThanInteger-04 = (UApp (UApp (UBuiltin lessThanInteger) (UCon (tagCon integer (ℤ.pos 4)))) (UCon (tagCon integer (ℤ.pos 4))))

expected-lessThanInteger-04 : Result
expected-lessThanInteger-04 = success (UCon (tagCon bool false))

_ : evalRaw test-lessThanInteger-04 ≡ expected-lessThanInteger-04
_ = refl
```

## lessThanInteger-05

```
-- builtin/semantics/lessThanInteger/lessThanInteger-05
test-lessThanInteger-05 : Untyped
test-lessThanInteger-05 = (UApp (UApp (UBuiltin lessThanInteger) (UCon (tagCon integer (ℤ.pos 3477349701412809834789938452452684373578934257)))) (UCon (tagCon integer (ℤ.pos 3477349701412809834789938452452684373578934257))))

expected-lessThanInteger-05 : Result
expected-lessThanInteger-05 = success (UCon (tagCon bool false))

_ : evalRaw test-lessThanInteger-05 ≡ expected-lessThanInteger-05
_ = refl
```
