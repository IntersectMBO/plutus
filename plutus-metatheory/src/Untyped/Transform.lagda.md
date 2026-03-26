---
title: Untyped.Transform
layout: page
---

# Utilities for term transformations


```
module Untyped.Transform where

open import Untyped
open import Untyped.Relation
open import Data.List using (List; []; _∷_)
open import Function using (case_of_)
open import Data.List.Relation.Binary.Pointwise
open import Data.Nat
open import Data.Maybe
open import Data.Fin
```

## Bottom-up traversals

Bottom-up traversal with a rewriting rule `f`. For later proofs, it turns out to be
useful to split out the definition in mutually recursive functions. One for the
part that recurses in the sub-terms, which we name `subterms`, and one for
recursing in lists of terms, which happens for `constr` and `case`.

`↑` is similar to `transformOf subterms` in Haskell

```
infixl 30 _↑_
infixl 30 _↑*_

_↑_ : (∀ {X} → X ⊢ → X ⊢) → ∀ {X} → X ⊢ → X ⊢
_↑*_ : (∀ {X} → X ⊢ → X ⊢) → ∀ {X} → List (X ⊢) → List (X ⊢)
subterms : (∀ {X} → X ⊢ → X ⊢) → ∀ {X} → X ⊢ → X ⊢

f ↑ M = f (subterms f M)

f ↑* [] = []
f ↑* (M ∷ Ms) = f ↑ M ∷ f ↑* Ms

subterms f M = case M of λ where
  (` x) → ` x
  (ƛ M) → ƛ (f ↑ M)
  (M · N) → (f ↑ M) · (f ↑ N)
  (force M) → force (f ↑ M)
  (delay M) → delay (f ↑ M)
  (con x) → con x
  (constr i Ms) → constr i (f ↑* Ms)
  (case M Ms) → case (f ↑ M) (f ↑* Ms)
  (builtin b) → builtin b
  error → error
```

With partial functions:


```
infixl 30 _⇑_
infixl 30 _⇑*_

_⇑_ : (∀ {X} → X ⊢ → Maybe (X ⊢)) → ∀ {X} → X ⊢ → X ⊢
_⇑*_ : (∀ {X} → X ⊢ → Maybe (X ⊢)) → ∀ {X} → List (X ⊢) → List (X ⊢)
sub : (∀ {X} → X ⊢ → Maybe (X ⊢)) → ∀ {X} → X ⊢ → X ⊢

f ⇑ M = let M' = sub f M
        in fromMaybe M' (f M')

f ⇑* [] = []
f ⇑* (M ∷ Ms) = f ⇑ M ∷ f ⇑* Ms

sub f M = case M of λ where
  (` x) → ` x
  (ƛ M) → ƛ (f ⇑ M)
  (M · N) → (f ⇑ M) · (f ⇑ N)
  (force M) → force (f ⇑ M)
  (delay M) → delay (f ⇑ M)
  (con x) → con x
  (constr i Ms) → constr i (f ⇑* Ms)
  (case M Ms) → case (f ⇑ M) (f ⇑* Ms)
  (builtin b) → builtin b
  error → error
```

## Properties

If `f` is extensive w.r.t a relation `_~_`, then so is `f ↑`.

```
module Extensive
  (_~_ : Relation)
  (~-trans : Transitive _~_)
  (~-compat : TermCompatible _~_)
  (f : Transform)
  (f-extensive : Extensive f _~_)
  where

  open TermCompatible ~-compat

  ↑-extensive : Extensive (f ↑_) _~_
  ↑*-extensive : ∀ {X} {Ms : List (X ⊢)} →
      Pointwise _~_ Ms (f ↑* Ms)
  subterms-extensive : Extensive (subterms f) _~_

  ↑-extensive {X} {M} = ~-trans subterms-extensive f-extensive 
  ↑*-extensive {Ms = []} = []
  ↑*-extensive {Ms = _ ∷ _} = ↑-extensive ∷ ↑*-extensive
  subterms-extensive {X} {M} with M
  ... | ` _ = compat-var
  ... | ƛ _ = compat-ƛ ↑-extensive
  ... | _ · _ = compat-· ↑-extensive ↑-extensive 
  ... | force _ = compat-force ↑-extensive
  ... | delay _ = compat-delay ↑-extensive
  ... | con _ = compat-con
  ... | constr i Ms = compat-constr ↑*-extensive
  ... | case M Ms = compat-case ↑-extensive ↑*-extensive
  ... | builtin _ = compat-builtin
  ... | error = compat-error
```

