---
title: Conformance.Term.ConstantCase.Unit
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term/constant-case/unit`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term.ConstantCase.Unit where

open import Conformance.Eval
```

## unit-01

```
-- term/constant-case/unit/unit-01
test-unit-01 : Untyped
test-unit-01 = (UCase (UCon (tagCon unit tt)) ((UCon (tagCon integer (ℤ.pos 42))) ∷ []))

expected-unit-01 : Result
expected-unit-01 = success (UCon (tagCon integer (ℤ.pos 42)))

_ : evalRaw test-unit-01 ≡ expected-unit-01
_ = refl
```

## unit-02

```
-- term/constant-case/unit/unit-02
-- casing constant only expects one branch
test-unit-02 : Untyped
test-unit-02 = (UCase (UCon (tagCon unit tt)) ([]))

expected-unit-02 : Result
expected-unit-02 = failure

_ : evalRaw test-unit-02 ≡ expected-unit-02
_ = refl
```

## unit-03

```
-- term/constant-case/unit/unit-03
-- casing constant only expects one branch
test-unit-03 : Untyped
test-unit-03 = (UCase (UCon (tagCon unit tt)) ((UCon (tagCon integer (ℤ.pos 42))) ∷ (UCon (tagCon integer (ℤ.pos 43))) ∷ []))

expected-unit-03 : Result
expected-unit-03 = failure

_ : evalRaw test-unit-03 ≡ expected-unit-03
_ = refl
```
