---
title: Untyped.Transform
layout: page
---

# Utilities for term transformations


```
module Untyped.Transform where

open import Untyped
open import Untyped.Relation.Binary
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

_↑_ : (∀ {n} → n ⊢ → n ⊢) → ∀ {n} → n ⊢ → n ⊢
_↑*_ : (∀ {n} → n ⊢ → n ⊢) → ∀ {n} → List (n ⊢) → List (n ⊢)
subterms : (∀ {n} → n ⊢ → n ⊢) → ∀ {n} → n ⊢ → n ⊢

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

_↑?_ : (∀ {n} → n ⊢ → Maybe (n ⊢)) → ∀ {n} → n ⊢ → n ⊢
_↑?*_ : (∀ {n} → n ⊢ → Maybe (n ⊢)) → ∀ {n} → List (n ⊢) → List (n ⊢)
sub : (∀ {n} → n ⊢ → Maybe (n ⊢)) → ∀ {n} → n ⊢ → n ⊢

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
  (f-refines : Refines f R)
  where

  open TermCompatible ~-compat

  ↑-refines : Refines (f ↑_) R
  ↑*-refines : ∀ {n} {Ms : List (n ⊢)} →
      Pointwise R Ms (f ↑* Ms)
  subterms-refines : Refines (subterms f) R

  ↑-refines {n} {M} = ~-trans subterms-refines f-refines 
  ↑*-refines {Ms = []} = []
  ↑*-refines {Ms = _ ∷ _} = ↑-refines ∷ ↑*-refines
  subterms-refines {n} {M} with M
  ... | ` _ = compat-var
  ... | ƛ _ = compat-ƛ ↑-refines
  ... | _ · _ = compat-· ↑-refines ↑-refines 
  ... | force _ = compat-force ↑-refines
  ... | delay _ = compat-delay ↑-refines
  ... | con _ = compat-con
  ... | constr i Ms = compat-constr ↑*-refines
  ... | case M Ms = compat-case ↑-refines ↑*-refines
  ... | builtin _ = compat-builtin
  ... | error = compat-error

module Refines?
  (R : Relation)
  (~-trans : Transitive R)
  (~-compat : TermCompatible R)
  (f : ∀ {n} → n ⊢ → Maybe (n ⊢))
  (f-refines? : Refines? f R)
  where

  open TermCompatible ~-compat

  ↑?-refines : Refines (f ↑?_) R
  ↑?*-refines : ∀ {n} {Ms : List (n ⊢)} →
      Pointwise R Ms (f ↑?* Ms)
  sub-refines : Refines (sub f) R

  ↑?-refines {n} {M} with sub-refines {_} {M}
  ... | sub-ext with f (sub f M) in eq
  ... | just M'' = ~-trans sub-ext (f-refines? _ _ eq)
  ... | nothing = sub-ext
  ↑?*-refines {Ms = []} = []
  ↑?*-refines {Ms = _ ∷ _} = ↑?-refines ∷ ↑?*-refines
  sub-refines {n} {M} with M
  ... | ` _ = compat-var
  ... | ƛ _ = compat-ƛ ↑?-refines
  ... | _ · _ = compat-· ↑?-refines ↑?-refines
  ... | force _ = compat-force ↑?-refines
  ... | delay _ = compat-delay ↑?-refines
  ... | con _ = compat-con
  ... | constr i Ms = compat-constr ↑?*-refines
  ... | case M Ms = compat-case ↑?-refines ↑?*-refines
  ... | builtin _ = compat-builtin
  ... | error = compat-error
```
