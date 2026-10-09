---
title: Conformance.Builtin.Semantics.ChooseUnit
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/chooseUnit`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ChooseUnit where

open import Conformance.Eval
```

## chooseUnit-01

```
-- builtin/semantics/chooseUnit/chooseUnit-01
test-chooseUnit-01 : Untyped
test-chooseUnit-01 = (UApp (UApp (UForce (UBuiltin chooseUnit)) (UCon (tagCon unit tt))) (UCon (tagCon integer (ℤ.pos 2))))

expected-chooseUnit-01 : Result
expected-chooseUnit-01 = success (UCon (tagCon integer (ℤ.pos 2)))

_ : evalRaw test-chooseUnit-01 ≡ expected-chooseUnit-01
_ = refl
```

## chooseUnit-02

```
-- builtin/semantics/chooseUnit/chooseUnit-02
-- chooseUnit should accept arbitrary terms for the second argument
test-chooseUnit-02 : Untyped
test-chooseUnit-02 = (UApp (UApp (UForce (UBuiltin chooseUnit)) (UCon (tagCon unit tt))) (ULambda (UVar 0)))

expected-chooseUnit-02 : Result
expected-chooseUnit-02 = success (ULambda (UVar 0))

_ : evalRaw test-chooseUnit-02 ≡ expected-chooseUnit-02
_ = refl
```
