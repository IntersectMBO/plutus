---
title: Conformance.Term.Case
layout: page
---

<!-- GENERATED FILE: do not edit.
     Regenerate with `generate-agda-conformance` from the nix shell, or with
     `cabal run plutus-conformance:generate-agda-conformance` from the
     repository root. -->

Conformance tests generated from
`plutus-conformance/test-cases/uplc/evaluation/term/case`.
See `Conformance.Eval` for how they are run.

```
module Conformance.Term.Case where

open import Conformance.Eval
```

## case-01

```
-- term/case/case-01
-- select first branch
test-case-01 : Untyped
test-case-01 = (UCase (UConstr 0 ((UCon (tagCon integer (ℤ.pos 0))) ∷ [])) ((ULambda (UCon (tagCon integer (ℤ.pos 1)))) ∷ (ULambda (UCon (tagCon integer (ℤ.pos 2)))) ∷ []))

expected-case-01 : Result
expected-case-01 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-case-01 ≡ expected-case-01
_ = refl
```

## case-02

```
-- term/case/case-02
-- select second branch
test-case-02 : Untyped
test-case-02 = (UCase (UConstr 1 ((UCon (tagCon integer (ℤ.pos 0))) ∷ [])) ((ULambda (UCon (tagCon integer (ℤ.pos 1)))) ∷ (ULambda (UCon (tagCon integer (ℤ.pos 2)))) ∷ []))

expected-case-02 : Result
expected-case-02 = success (UCon (tagCon integer (ℤ.pos 2)))

_ : evalRaw test-case-02 ≡ expected-case-02
_ = refl
```

## case-03

```
-- term/case/case-03
-- select first branch and do computation with the args
test-case-03 : Untyped
test-case-03 = (UCase (UConstr 0 ((UCon (tagCon integer (ℤ.pos 3))) ∷ (UCon (tagCon integer (ℤ.pos 2))) ∷ [])) ((ULambda (ULambda (UApp (UApp (UBuiltin addInteger) (UVar 1)) (UVar 0)))) ∷ (ULambda (ULambda (UApp (UApp (UBuiltin subtractInteger) (UVar 1)) (UVar 0)))) ∷ []))

expected-case-03 : Result
expected-case-03 = success (UCon (tagCon integer (ℤ.pos 5)))

_ : evalRaw test-case-03 ≡ expected-case-03
_ = refl
```

## case-04

```
-- term/case/case-04
-- select second branch and do computation with the args
test-case-04 : Untyped
test-case-04 = (UCase (UConstr 1 ((UCon (tagCon integer (ℤ.pos 3))) ∷ (UCon (tagCon integer (ℤ.pos 2))) ∷ [])) ((ULambda (ULambda (UApp (UApp (UBuiltin addInteger) (UVar 1)) (UVar 0)))) ∷ (ULambda (ULambda (UApp (UApp (UBuiltin subtractInteger) (UVar 1)) (UVar 0)))) ∷ []))

expected-case-04 : Result
expected-case-04 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-case-04 ≡ expected-case-04
_ = refl
```

## case-05

```
-- term/case/case-05
-- case of non-constr
test-case-05 : Untyped
test-case-05 = (UCase (ULambda (UVar 0)) ((ULambda (UVar 0)) ∷ (ULambda (UVar 0)) ∷ []))

expected-case-05 : Result
expected-case-05 = failure

_ : evalRaw test-case-05 ≡ expected-case-05
_ = refl
```

## case-06

```
-- term/case/case-06
-- branch with wrong arguments
test-case-06 : Untyped
test-case-06 = (UCase (UConstr 0 ((UCon (tagCon integer (ℤ.pos 0))) ∷ [])) ((UCon (tagCon integer (ℤ.pos 1))) ∷ (ULambda (UCon (tagCon integer (ℤ.pos 2)))) ∷ []))

expected-case-06 : Result
expected-case-06 = failure

_ : evalRaw test-case-06 ≡ expected-case-06
_ = refl
```

## case-07

Skipped: the program does not parse or has free variables (`parse/decode error`).

## case-08

```
-- term/case/case-08
-- nullary case
test-case-08 : Untyped
test-case-08 = (UCase (UConstr 0 ([])) ((UCon (tagCon integer (ℤ.pos 1))) ∷ (UCon (tagCon integer (ℤ.pos 2))) ∷ []))

expected-case-08 : Result
expected-case-08 = success (UCon (tagCon integer (ℤ.pos 1)))

_ : evalRaw test-case-08 ≡ expected-case-08
_ = refl
```

## case-09

```
-- term/case/case-09
-- It's legal to have a case term with no branches, but using it to branch on
-- any `constr` term will cause an error, so this will fail.
test-case-09 : Untyped
test-case-09 = (UCase (UConstr 0 ([])) ([]))

expected-case-09 : Result
expected-case-09 = failure

_ : evalRaw test-case-09 ≡ expected-case-09
_ = refl
```

## case-10

```
-- term/case/case-10
-- This should not fail: a case expression with an empty list of branches is
-- legal (but attempting to use it to branch on any `constr` term will cause an
-- error).
test-case-10 : Untyped
test-case-10 = (ULambda (UCase (UVar 0) ([])))

expected-case-10 : Result
expected-case-10 = success (ULambda (UCase (UVar 0) ([])))

_ : evalRaw test-case-10 ≡ expected-case-10
_ = refl
```
