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
open import Data.Nat
open import Data.Maybe
open import Data.Fin
open import Relation.Binary.PropositionalEquality
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
infixl 30 _↑?_
infixl 30 _↑?*_

_↑?_ : (∀ {X} → X ⊢ → Maybe (X ⊢)) → ∀ {X} → X ⊢ → X ⊢
_↑?*_ : (∀ {X} → X ⊢ → Maybe (X ⊢)) → ∀ {X} → List (X ⊢) → List (X ⊢)
sub : (∀ {X} → X ⊢ → Maybe (X ⊢)) → ∀ {X} → X ⊢ → X ⊢

f ↑? M = let M' = sub f M
        in fromMaybe M' (f M')

f ↑?* [] = []
f ↑?* (M ∷ Ms) = f ↑? M ∷ f ↑?* Ms

sub f M = case M of λ where
  (` x) → ` x
  (ƛ M) → ƛ (f ↑? M)
  (M · N) → (f ↑? M) · (f ↑? N)
  (force M) → force (f ↑? M)
  (delay M) → delay (f ↑? M)
  (con x) → con x
  (constr i Ms) → constr i (f ↑?* Ms)
  (case M Ms) → case (f ↑? M) (f ↑?* Ms)
  (builtin b) → builtin b
  error → error
```

## Properties

If `f` refines `R`, then so does `f ↑`.

```
module Refines
  (R : Relation)
  (~-trans : Transitive R)
  (~-compat : TermCompatible R)
  (f : Transform)
  (f-relating : Refines f R)
  where

  open TermCompatible ~-compat

  ↑-relating : Refines (f ↑_) R
  ↑*-relating : ∀ {X} {Ms : List (X ⊢)} →
      Pointwise R Ms (f ↑* Ms)
  subterms-relating : Refines (subterms f) R

  ↑-relating {X} {M} = ~-trans subterms-relating f-relating 
  ↑*-relating {Ms = []} = []
  ↑*-relating {Ms = _ ∷ _} = ↑-relating ∷ ↑*-relating
  subterms-relating {X} {M} with M
  ... | ` _ = compat-var
  ... | ƛ _ = compat-ƛ ↑-relating
  ... | _ · _ = compat-· ↑-relating ↑-relating 
  ... | force _ = compat-force ↑-relating
  ... | delay _ = compat-delay ↑-relating
  ... | con _ = compat-con
  ... | constr i Ms = compat-constr ↑*-relating
  ... | case M Ms = compat-case ↑-relating ↑*-relating
  ... | builtin _ = compat-builtin
  ... | error = compat-error

module Refines?
  (R : Relation)
  (~-trans : Transitive R)
  (~-compat : TermCompatible R)
  (f : ∀ {X} → X ⊢ → Maybe (X ⊢))
  (f-relating? : Refines? f R)
  where

  open TermCompatible ~-compat

  ↑?-relating : Refines (f ↑?_) R
  ↑?*-relating : ∀ {X} {Ms : List (X ⊢)} →
      Pointwise R Ms (f ↑?* Ms)
  sub-relating : Refines (sub f) R

  ↑?-relating {X} {M} with sub-relating {_} {M}
  ... | sub-ext with f (sub f M) in eq
  ... | just M'' = ~-trans sub-ext (f-relating? _ eq)
  ... | nothing = sub-ext
  ↑?*-relating {Ms = []} = []
  ↑?*-relating {Ms = _ ∷ _} = ↑?-relating ∷ ↑?*-relating
  sub-relating {X} {M} with M
  ... | ` _ = compat-var
  ... | ƛ _ = compat-ƛ ↑?-relating
  ... | _ · _ = compat-· ↑?-relating ↑?-relating
  ... | force _ = compat-force ↑?-relating
  ... | delay _ = compat-delay ↑?-relating
  ... | con _ = compat-con
  ... | constr i Ms = compat-constr ↑?*-relating
  ... | case M Ms = compat-case ↑?-relating ↑?*-relating
  ... | builtin _ = compat-builtin
  ... | error = compat-error
```
