---
title: Conformance.Eval
layout: page
---

Support for the generated conformance unit tests under `Conformance.*`.

The modules under `Conformance` are generated from the UPLC evaluation
conformance test cases in `plutus-conformance/test-cases/uplc/evaluation` by

    cabal run plutus-conformance:generate-agda-conformance

(run from the repository root) and must not be edited by hand. Each test case
becomes a `refl` proof that evaluating the program with the untyped CEK
machine gives the expected result, or, when the case involves constants or
builtins that are still postulated and so cannot reduce at type-checking time,
a *pending* statement of that proposition which is type-checked but not proved.
This module provides the evaluator wrapper and re-exports everything the
generated code refers to.

```
module Conformance.Eval where

open import Data.Unit public using (tt)
open import Data.Bool public using (true; false)
open import Data.Integer public using (ℤ)
open import Relation.Binary.PropositionalEquality public using (_≡_; refl)

open import Utils public
  using (List; _×_; _,_; DATA; mkByteString; mkArray; valueFromList)
open Utils.List public
open Utils.DATA public

open import RawU public using (Untyped; TagCon; Tag)
open RawU.Untyped public
open RawU.TagCon public
open RawU.Tag public

open import Builtin public using (Builtin)
open Builtin.Builtin public
```

## Evaluation

A closed raw term is scope-checked, run through the untyped CEK machine with
the same step budget as the compiled evaluator, and the resulting value is
discharged and converted back to a raw term. Every way of failing (scope error,
evaluation error, running out of steps) is collapsed into `failure`, which is
what the conformance tests mean by `evaluation failure`.

```
open import Utils using (Either; inj₁; inj₂)
open import Untyped using (_⊢; scopeCheckU0; extricateU0)
open import Untyped.CEK using (stepper; ε; []; _;_▻_; □; discharge)
open import Evaluator.Base using (maxsteps)

data Result : Set where
  failure : Result
  success : Untyped → Result

evalRaw : Untyped → Result
evalRaw raw with scopeCheckU0 raw
... | inj₁ _ = failure
... | inj₂ t with stepper maxsteps (ε ; [] ▻ t)
... | inj₂ (□ v) = success (extricateU0 (discharge v))
... | _          = failure
```

## Pending tests

`Pending P` is just `P`. A generated module states `Pending (evalRaw t ≡ r)`
as a type, without proving it, for cases that cannot be decided by `refl` yet.
This still checks that the terms are well-formed, and once the case can be
proved, regenerating only replaces that statement with a `refl` proof; the
program and expected result stay unchanged.

```
Pending : Set → Set
Pending P = P
```
