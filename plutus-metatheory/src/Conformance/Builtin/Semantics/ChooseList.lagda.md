---
title: Conformance.Builtin.Semantics.ChooseList
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/chooseList`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.ChooseList where

open import Conformance.Eval
```

## chooseList-01

```
-- builtin/semantics/chooseList/chooseList-01
test-chooseList-01 : Untyped
test-chooseList-01 = (UApp (UApp (UApp (UForce (UForce (UBuiltin chooseList))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ (ℤ.pos 1) ∷ (ℤ.pos 2) ∷ [])))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 2))))

expected-chooseList-01 : Result
expected-chooseList-01 = success (UCon (tagCon integer (ℤ.pos 2)))

_ : evalRaw test-chooseList-01 ≡ expected-chooseList-01
_ = refl
```

## chooseList-02

```
-- builtin/semantics/chooseList/chooseList-02
test-chooseList-02 : Untyped
test-chooseList-02 = (UApp (UApp (UApp (UForce (UForce (UBuiltin chooseList))) (UCon (tagCon (list integer) ([])))) (UCon (tagCon integer (ℤ.pos 1)))) (UCon (tagCon integer (ℤ.pos 2))))

expected-chooseList-02 : Result
expected-chooseList-02 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-chooseList-02 ≡ expected-chooseList-02
_ = refl
```

## chooseList-03

```
-- builtin/semantics/chooseList/chooseList-03
-- chooseList should accept arbitrary terms in the branches
test-chooseList-03 : Untyped
test-chooseList-03 = (UApp (UApp (UApp (UForce (UForce (UBuiltin chooseList))) (UCon (tagCon (list integer) ((ℤ.pos 0) ∷ (ℤ.pos 1) ∷ (ℤ.pos 2) ∷ [])))) (ULambda (UVar 0))) (ULambda (ULambda (UVar 0))))

expected-chooseList-03 : Result
expected-chooseList-03 = success (ULambda (ULambda (UVar 0)))

_ : evalRaw test-chooseList-03 ≡ expected-chooseList-03
_ = refl
```

## chooseList-04

```
-- builtin/semantics/chooseList/chooseList-04
-- chooseList should accept arbitrary terms in the branches
test-chooseList-04 : Untyped
test-chooseList-04 = (UApp (UApp (UApp (UForce (UForce (UBuiltin chooseList))) (UCon (tagCon (list integer) ([])))) (ULambda (UVar 0))) (ULambda (ULambda (UVar 0))))

expected-chooseList-04 : Result
expected-chooseList-04 = success (ULambda (UVar 0))

_ : evalRaw test-chooseList-04 ≡ expected-chooseList-04
_ = refl
```
