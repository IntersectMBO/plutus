---
title: Conformance.Builtin.Semantics.NullList
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/builtin/semantics/nullList`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Builtin.Semantics.NullList where

open import Conformance.Eval
```

## nullList-01

```
-- builtin/semantics/nullList/nullList-01
test-nullList-01 : Untyped
test-nullList-01 = (UApp (UForce (UBuiltin nullList)) (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 2) ∷ (ℤ.pos 3) ∷ []))))

expected-nullList-01 : Result
expected-nullList-01 = success (UCon (tagCon bool false))

_ : evalRaw test-nullList-01 ≡ expected-nullList-01
_ = refl
```

## nullList-02

```
-- builtin/semantics/nullList/nullList-02
test-nullList-02 : Untyped
test-nullList-02 = (UApp (UForce (UBuiltin nullList)) (UCon (tagCon (list integer) ([]))))

expected-nullList-02 : Result
expected-nullList-02 = success (UCon (tagCon bool true))

_ : evalRaw test-nullList-02 ≡ expected-nullList-02
_ = refl
```
