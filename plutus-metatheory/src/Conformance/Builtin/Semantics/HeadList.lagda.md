---
title: Conformance.Builtin.Semantics.HeadList
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/headList`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.HeadList where

open import Conformance.Eval
```

## headList-01

```
-- builtin/semantics/headList/headList-01
test-headList-01 : Untyped
test-headList-01 = (UApp (UForce (UBuiltin headList)) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 2) ∷ []))))

expected-headList-01 : Result
expected-headList-01 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-headList-01 ≡ expected-headList-01
_ = refl
```

## headList-02

```
-- builtin/semantics/headList/headList-02
test-headList-02 : Untyped
test-headList-02 = (UApp (UForce (UBuiltin headList)) (UCon (tagCon (list integer) ([]))))

expected-headList-02 : Result
expected-headList-02 = failure

_ : evalRaw test-headList-02 ≡ expected-headList-02
_ = refl
```

## headList-03

```
-- builtin/semantics/headList/headList-03
test-headList-03 : Untyped
test-headList-03 = (UApp (UForce (UBuiltin headList)) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 2) ∷ (ℤ.pos 3) ∷ []))))

expected-headList-03 : Result
expected-headList-03 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-headList-03 ≡ expected-headList-03
_ = refl
```

## headPartial

```
-- builtin/semantics/headList/headPartial
-- head is partial like haskell's and blows up when given an empty list
test-headPartial : Untyped
test-headPartial = (UApp (UForce (UBuiltin headList)) (UApp (UBuiltin mkNilData) (UCon (tagCon unit tt))))

expected-headPartial : Result
expected-headPartial = failure

_ : evalRaw test-headPartial ≡ expected-headPartial
_ = refl
```
