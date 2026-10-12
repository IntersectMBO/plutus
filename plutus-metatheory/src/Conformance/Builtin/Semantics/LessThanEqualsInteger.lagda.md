---
title: Conformance.Builtin.Semantics.LessThanEqualsInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/lessThanEqualsInteger`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.LessThanEqualsInteger where

open import Conformance.Eval
```

## lessThanEqualsInteger-01

```
-- builtin/semantics/lessThanEqualsInteger/lessThanEqualsInteger-01
test-lessThanEqualsInteger-01 : Untyped
test-lessThanEqualsInteger-01 = (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 2))))

expected-lessThanEqualsInteger-01 : Result
expected-lessThanEqualsInteger-01 = success (UCon (tagCon bool true))

_ : evalRaw test-lessThanEqualsInteger-01 ≡ expected-lessThanEqualsInteger-01
_ = refl
```

## lessThanEqualsInteger-02

```
-- builtin/semantics/lessThanEqualsInteger/lessThanEqualsInteger-02
test-lessThanEqualsInteger-02 : Untyped
test-lessThanEqualsInteger-02 = (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 8)))) (UCon (tagCon integer (ℤ.pos 4))))

expected-lessThanEqualsInteger-02 : Result
expected-lessThanEqualsInteger-02 = success (UCon (tagCon bool false))

_ : evalRaw test-lessThanEqualsInteger-02 ≡ expected-lessThanEqualsInteger-02
_ = refl
```

## lessThanEqualsInteger-03

```
-- builtin/semantics/lessThanEqualsInteger/lessThanEqualsInteger-03
test-lessThanEqualsInteger-03 : Untyped
test-lessThanEqualsInteger-03 = (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 4)))) (UCon (tagCon integer (ℤ.pos 8))))

expected-lessThanEqualsInteger-03 : Result
expected-lessThanEqualsInteger-03 = success (UCon (tagCon bool true))

_ : evalRaw test-lessThanEqualsInteger-03 ≡ expected-lessThanEqualsInteger-03
_ = refl
```

## lessThanEqualsInteger-04

```
-- builtin/semantics/lessThanEqualsInteger/lessThanEqualsInteger-04
test-lessThanEqualsInteger-04 : Untyped
test-lessThanEqualsInteger-04 = (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 4)))) (UCon (tagCon integer (ℤ.pos 4))))

expected-lessThanEqualsInteger-04 : Result
expected-lessThanEqualsInteger-04 = success (UCon (tagCon bool true))

_ : evalRaw test-lessThanEqualsInteger-04 ≡ expected-lessThanEqualsInteger-04
_ = refl
```

## lessThanEqualsInteger-05

```
-- builtin/semantics/lessThanEqualsInteger/lessThanEqualsInteger-05
test-lessThanEqualsInteger-05 : Untyped
test-lessThanEqualsInteger-05 = (UApp (UApp (UBuiltin lessThanEqualsInteger) (UCon (tagCon integer (ℤ.pos 3477349701412809834789938452452684373578934257)))) (UCon (tagCon integer (ℤ.pos 3477349701412809834789938452452684373578934257))))

expected-lessThanEqualsInteger-05 : Result
expected-lessThanEqualsInteger-05 = success (UCon (tagCon bool true))

_ : evalRaw test-lessThanEqualsInteger-05 ≡ expected-lessThanEqualsInteger-05
_ = refl
```
