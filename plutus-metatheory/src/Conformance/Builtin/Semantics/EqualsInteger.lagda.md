---
title: Conformance.Builtin.Semantics.EqualsInteger
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/equalsInteger`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.EqualsInteger where

open import Conformance.Eval
```

## equalsInteger-01

```
-- builtin/semantics/equalsInteger/equalsInteger-01
test-equalsInteger-01 : Untyped
test-equalsInteger-01 = (UApp (UApp (UBuiltin equalsInteger) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 2))))

expected-equalsInteger-01 : Result
expected-equalsInteger-01 = success (UCon (tagCon bool false))

_ : evalRaw test-equalsInteger-01 ≡ expected-equalsInteger-01
_ = refl
```

## equalsInteger-02

```
-- builtin/semantics/equalsInteger/equalsInteger-02
test-equalsInteger-02 : Untyped
test-equalsInteger-02 = (UApp (UApp (UBuiltin equalsInteger) (UCon (tagCon integer (ℤ.pos 45723452347050234588234852993485827934)))) (UCon (tagCon integer (ℤ.pos 45723452347050234588234852993485827933))))

expected-equalsInteger-02 : Result
expected-equalsInteger-02 = success (UCon (tagCon bool false))

_ : evalRaw test-equalsInteger-02 ≡ expected-equalsInteger-02
_ = refl
```

## equalsInteger-03

```
-- builtin/semantics/equalsInteger/equalsInteger-03
test-equalsInteger-03 : Untyped
test-equalsInteger-03 = (UApp (UApp (UBuiltin equalsInteger) (UCon (tagCon integer (ℤ.pos 45723452347050234588234852993485827934)))) (UCon (tagCon integer (ℤ.pos 45723452347050234588234852993485827934))))

expected-equalsInteger-03 : Result
expected-equalsInteger-03 = success (UCon (tagCon bool true))

_ : evalRaw test-equalsInteger-03 ≡ expected-equalsInteger-03
_ = refl
```
