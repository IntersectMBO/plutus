---
title: Conformance.Term.ConstantCase.Pair
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term/constant-case/pair`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term.ConstantCase.Pair where

open import Conformance.Eval
```

## pair-01

```
-- term/constant-case/pair/pair-01
test-pair-01 : Untyped
test-pair-01 = (UCase (UCon (tagCon (pair integer bool) ((ℤ.pos 42) , false))) ((ULambda (ULambda (UVar 1))) ∷ []))

expected-pair-01 : Result
expected-pair-01 = success (UCon (tagCon integer (ℤ.pos 42)))

_ : evalRaw test-pair-01 ≡ expected-pair-01
_ = refl
```

## pair-02

```
-- term/constant-case/pair/pair-02
test-pair-02 : Untyped
test-pair-02 = (UCase (UCon (tagCon (pair integer bool) ((ℤ.pos 42) , false))) ((ULambda (ULambda (UVar 0))) ∷ []))

expected-pair-02 : Result
expected-pair-02 = success (UCon (tagCon bool false))

_ : evalRaw test-pair-02 ≡ expected-pair-02
_ = refl
```

## pair-03

```
-- term/constant-case/pair/pair-03
-- Casing on pair expects exactly one branch
test-pair-03 : Untyped
test-pair-03 = (UCase (UCon (tagCon (pair integer bool) ((ℤ.pos 42) , false))) ([]))

expected-pair-03 : Result
expected-pair-03 = failure

_ : evalRaw test-pair-03 ≡ expected-pair-03
_ = refl
```

## pair-04

```
-- term/constant-case/pair/pair-04
-- Casing on pair expects exactly one branch
test-pair-04 : Untyped
test-pair-04 = (UCase (UCon (tagCon (pair integer bool) ((ℤ.pos 42) , false))) ((ULambda (ULambda (UVar 0))) ∷ (ULambda (ULambda (UVar 0))) ∷ []))

expected-pair-04 : Result
expected-pair-04 = failure

_ : evalRaw test-pair-04 ≡ expected-pair-04
_ = refl
```

## pair-05

```
-- term/constant-case/pair/pair-05
-- Casing on pair expects branch to take two arguments
test-pair-05 : Untyped
test-pair-05 = (UCase (UCon (tagCon (pair integer bool) ((ℤ.pos 42) , false))) ((ULambda (UVar 0)) ∷ []))

expected-pair-05 : Result
expected-pair-05 = failure

_ : evalRaw test-pair-05 ≡ expected-pair-05
_ = refl
```
