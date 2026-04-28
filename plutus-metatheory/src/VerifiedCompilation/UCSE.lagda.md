---
title: VerifiedCompilation.UCSE
layout: page
---

# Common Subexpression Elimination Translation Phase
```
module VerifiedCompilation.UCSE where

```
## Imports

```
open import VerifiedCompilation.UntypedViews
open import VerifiedCompilation.UntypedTranslation using (Translation; TransMatch; translation?; Relation)
import Relation.Binary as Binary using (Decidable)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error; Let_In_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin; suc; zero)
open import Untyped.RenamingSubstitution using (_[_])
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; pcePointwise; DecidableCE; CseT; isProof?)
open import Data.Bool.Base using (Bool; false; true)
open import Data.List hiding ([_])
open import Untyped.Strictness

```
## Description

This module is required to certify that an application of CSE doesn't break the
semantics; we are explicitly not evaluating whether the particular choice of
sub-expression was a "good" choice.

The `UCSE` translation relation has a single constructor `cse`. A term `x` translates
to `Let e In x'` when:

1. Substituting `e` back into `x'` yields a term that `UCSE`-translates from `x`,
   so the transformation is locally invertible up to further CSE steps.

2. `zero` (the variable bound by the `let`) lies on an execution path through `x'`,
   as witnessed by `∈↓`, a predicate that holds when a variable lies
   on at least one execution path through a term. This guarantees soundness: the
   transformed term is no less strict than the original.

```

private variable
  n : ℕ

data UCSE : Relation where
  cse : {x' : suc n ⊢} {x e : n ⊢}
    → zero ∈↓ x'
    → Translation UCSE x (x' [ e ])
    → UCSE x (Let e In x')

UntypedCSE : (ast : n ⊢) → (ast' : n ⊢) → Set
UntypedCSE = Translation UCSE

```

## Decision Procedure

`isUCSE?` decides `UCSE` by checking that the output is a `let`-binding, that `zero`
occurs on an execution path through the body, and that the result of back-substitution
is accepted by `isUntypedCSE?`.

```

isUntypedCSE? : DecidableCE (Translation UCSE {n})

{-# TERMINATING #-}
isUCSE? : DecidableCE (UCSE {n})

isUCSE? ast₁ ast₂ with (Let? ⋯ In? ⋯) ast₂ 
... | no ¬letMatch = ce (λ { (cse x x₁) → ¬letMatch inhabitant}) CseT ast₁ ast₂
... | yes (Let! match! rhs In! match! body) with zero ∈↓? body
...   | no ¬onPath = ce (λ { (cse x x₁) → ¬onPath x }) CseT ast₁ ast₂
...   | yes onPath with (isUntypedCSE? ast₁ (body [ rhs ]))
...     | ce ¬isCSE tag t₁ t₂ = ce (λ { (cse x x₁) → ¬isCSE x₁ }) tag t₁ t₂
...     | proof isCSE = proof (cse onPath isCSE)

isUntypedCSE? = translation? CseT isUCSE?
```

## Tests

A few unit tests which check that the decision procedure works as expected.

The third test shows that the strictness condition catches an unsound transformation.

```

M₁ : 1 ⊢
M₁ = constr 0 [] · constr 0 []

N₁ : 1 ⊢
N₁ = Let constr 0 [] In ` zero · ` zero

_ : isProof? (isUntypedCSE? M₁ N₁) ≡ true
_ = refl

M₂ : 1 ⊢
M₂ = Let constr 0 [] In ` zero

N₂ : 1 ⊢
N₂ = Let constr 0 [] In ` zero

_ : isProof? (isUntypedCSE? M₂ N₂) ≡ true
_ = refl

M₃ : 1 ⊢
M₃ = constr 0 []

N₃ : 1 ⊢
N₃ = Let error In constr 0 []

_ : isProof? (isUntypedCSE? M₃ N₃) ≡ false
_ = refl

```
