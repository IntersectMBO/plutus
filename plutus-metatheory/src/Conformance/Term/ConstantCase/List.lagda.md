---
title: Conformance.Term.ConstantCase.List
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `cabal run plutus-conformance:generate-agda-conformance`
     from the repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term/constant-case/list`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term.ConstantCase.List where

open import Conformance.Eval
```

## list-01

```
-- term/constant-case/list/list-01
-- case on non-empty list with two branches
test-list-01 : Untyped
test-list-01 = (UCase (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 2) ∷ (ℤ.pos 3) ∷ (ℤ.pos 4) ∷ []))) ((ULambda (ULambda (UVar 1))) ∷ (UCon (tagCon integer (ℤ.negsuc 0))) ∷ []))

expected-list-01 : Result
expected-list-01 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-list-01 ≡ expected-list-01
_ = refl
```

## list-02

```
-- term/constant-case/list/list-02
-- case on empty list with two branches
test-list-02 : Untyped
test-list-02 = (UCase (UCon (tagCon (list integer) ([]))) ((ULambda (ULambda (UVar 1))) ∷ (UCon (tagCon integer (ℤ.negsuc 0))) ∷ []))

expected-list-02 : Result
expected-list-02 = success (UCon (tagCon integer (ℤ.negsuc 0)))

_ : evalRaw test-list-02 ≡ expected-list-02
_ = refl
```

## list-03

```
-- term/constant-case/list/list-03
-- case on non-empty list with one branch
test-list-03 : Untyped
test-list-03 = (UCase (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 2) ∷ (ℤ.pos 3) ∷ (ℤ.pos 4) ∷ []))) ((ULambda (ULambda (UVar 1))) ∷ []))

expected-list-03 : Result
expected-list-03 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-list-03 ≡ expected-list-03
_ = refl
```

## list-04

```
-- term/constant-case/list/list-04
-- case on empty list with one branch
test-list-04 : Untyped
test-list-04 = (UCase (UCon (tagCon (list integer) ([]))) ((ULambda (ULambda (UVar 1))) ∷ []))

expected-list-04 : Result
expected-list-04 = failure

_ : evalRaw test-list-04 ≡ expected-list-04
_ = refl
```

## list-05

```
-- term/constant-case/list/list-05
-- case on non-empty list with one incorrectly typed branch
test-list-05 : Untyped
test-list-05 = (UCase (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 2) ∷ (ℤ.pos 3) ∷ (ℤ.pos 4) ∷ []))) ((UCon (tagCon integer (ℤ.negsuc 0))) ∷ []))

expected-list-05 : Result
expected-list-05 = failure

_ : evalRaw test-list-05 ≡ expected-list-05
_ = refl
```

## list-06

```
-- term/constant-case/list/list-06
-- case on non-empty list with two incorrectly typed branch
test-list-06 : Untyped
test-list-06 = (UCase (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 2) ∷ (ℤ.pos 3) ∷ (ℤ.pos 4) ∷ []))) ((UCon (tagCon integer (ℤ.negsuc 0))) ∷ (UCon (tagCon integer (ℤ.negsuc 0))) ∷ []))

expected-list-06 : Result
expected-list-06 = failure

_ : evalRaw test-list-06 ≡ expected-list-06
_ = refl
```

## list-07

```
-- term/constant-case/list/list-07
-- case on empty list with two incorrectly typed branch
test-list-07 : Untyped
test-list-07 = (UCase (UCon (tagCon (list integer) ((ℤ.pos 1) ∷ (ℤ.pos 2) ∷ (ℤ.pos 3) ∷ (ℤ.pos 4) ∷ []))) ((UCon (tagCon integer (ℤ.negsuc 0))) ∷ (ULambda (ULambda (UVar 1))) ∷ []))

expected-list-07 : Result
expected-list-07 = failure

_ : evalRaw test-list-07 ≡ expected-list-07
_ = refl
```
