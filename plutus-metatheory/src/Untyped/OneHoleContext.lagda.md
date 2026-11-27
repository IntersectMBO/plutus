---
title: One Hole Contexts
layout: page
---

```
module Untyped.OneHoleContext where
```

## Imports and variables

```
open import Untyped
open import Untyped.RenamingSubstitution
open import Data.Nat
open import Data.List
open import Data.Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

private variable
  n m l : ℕ
  M : n ⊢
```

## Contexts

A context `C : m ⊸ n ⊢` has a single hole `□` that is a placeholder for a term
of type `m ⊢` to obtain a term of `n ⊢`.

```
data _⊸_⊢ : ℕ → ℕ → Set where

  □ : n ⊸ n ⊢

  ƛ
    : m ⊸ suc n ⊢
    → m ⊸ n ⊢

  _·ₗ_
    : m ⊸ n ⊢
    → n ⊢
    → m ⊸ n ⊢

  _·ᵣ_
    : n ⊢
    → m ⊸ n ⊢
    → m ⊸ n ⊢

  force
    : m ⊸ n ⊢
    → m ⊸ n ⊢

  delay
    : m ⊸ n ⊢
    → m ⊸ n ⊢

  constr : ∀ {m n}
    → ℕ
    → List (n ⊢)
    → m ⊸ n ⊢
    → List (n ⊢)
    → m ⊸ n ⊢

  caseₗ : ∀ {m n}
    → m ⊸ n ⊢
    → List (n ⊢)
    → m ⊸ n ⊢

  caseᵣ : ∀ {m n}
    → n ⊢
    → List (n ⊢)
    → m ⊸ n ⊢
    → List (n ⊢)
    → m ⊸ n ⊢

private variable
  C D : n ⊸ m ⊢
```

## Plugging

Replace the hole by an (open) term.
```
infix 9 _⟨_⟩
_⟨_⟩ : m ⊸ n ⊢ → m ⊢ → n ⊢
□ ⟨ t ⟩ = t
(ƛ C) ⟨ t ⟩ = ƛ (C ⟨ t ⟩)
(C ·ₗ u) ⟨ t ⟩ = (C ⟨ t ⟩) · u
(u ·ᵣ C) ⟨ t ⟩ = u · (C ⟨ t ⟩)
(force C) ⟨ t ⟩ = force (C ⟨ t ⟩)
(delay C) ⟨ t ⟩ = delay (C ⟨ t ⟩)
(constr i xs C ys) ⟨ t ⟩ = constr i (xs ++ ((C ⟨ t ⟩) ∷ ys))
(caseₗ C xs) ⟨ t ⟩ = case (C ⟨ t ⟩) xs
(caseᵣ u xs C ys) ⟨ t ⟩ = case u (xs ++ ((C ⟨ t ⟩) ∷ ys))
```

## Composition of contexts

Replace the hole in `C` by another context `D`.

```
infixr 9 _∘_

_∘_ : n ⊸ l ⊢
    → m ⊸ n ⊢
    → m ⊸ l ⊢
□ ∘ D = D
(ƛ C) ∘ D = ƛ (C ∘ D)
(C ·ₗ u) ∘ D = (C ∘ D) ·ₗ u
(u ·ᵣ C) ∘ D = u ·ᵣ (C ∘ D)
(force C) ∘ D = force (C ∘ D)
(delay C) ∘ D = delay (C ∘ D)
(constr i xs C ys) ∘ D = constr i xs (C ∘ D) ys
(caseₗ C xs) ∘ D = caseₗ (C ∘ D) xs
(caseᵣ u xs C ys) ∘ D = caseᵣ u xs (C ∘ D) ys
```

## Properties

It doesn't matter if you
- compose `C` and `D`, then plug in `M`
- or plug `M` into `D`, then plug the result in `C`

```
plug-compose : (C ∘ D) ⟨ M ⟩ ≡ C ⟨ D ⟨ M ⟩ ⟩
plug-compose {C = C} = go C
  where
    go : {m n : ℕ}
       → (C : m ⊸ n ⊢)
       → {D : l ⊸ m ⊢}
       → (C ∘ D) ⟨ M ⟩ ≡ C ⟨ D ⟨ M ⟩ ⟩
    go □ = refl
    go (ƛ C) = cong ƛ (go C)
    go (C ·ₗ M) = cong (_· M) (go C)
    go (M ·ᵣ C) = cong (M ·_) (go C)
    go (force C) = cong force (go C)
    go (delay C) = cong delay (go C)
    go (constr i Ms C Ms') = cong (λ M → constr i (Ms ++ M ∷ Ms')) (go C)
    go (caseₗ C Ms) = cong (λ M → case M Ms) (go C)
    go (caseᵣ M Ns C Ns') = cong (λ N → case M (Ns ++ N ∷ Ns')) (go C)
```

## Contextual equivalence

With respect to some equivalence on closed terms.

```
module ContextualEquivalence
  (_≐_ : 0 ⊢ → 0 ⊢ → Set)
  (let infix 4 _≐_; _≐_ = _≐_)
  where

  _≅_ : n ⊢ → n ⊢ → Set
  M ≅ N = ∀ C → C ⟨ M ⟩ ≐ C ⟨ N ⟩
```


## Small-step term transformations

```
module FocusExample where
```

A plugged one-hole-context lets us focus on a specific sub term, exactly like a
zipper. Consider this example term.

```
  M₀ : 0 ⊢
  M₀ = ƛ (` zero · ` zero)
```

We can focus on the first variable by "factoring out" a one-hole context and the
subterm.

```
  M₀' : 0 ⊢
  M₀' = (ƛ (□ ·ₗ ` zero)) ⟨ ` zero ⟩

  _ : M₀ ≡ M₀'
  _ = refl
```

This is useful for specifying how to do local transformation to a term. We could
define a replacement step that replaces some sub term `M` by another term `N`.

```
  infix 4 _↝_

  data _↝_ : 0 ⊢ → 0 ⊢ → Set where
    replace :
      {M N : m ⊢}
      (C : m ⊸ 0 ⊢)
      → C ⟨ M ⟩ ↝  C ⟨ N ⟩

  ID : 1 ⊢
  ID = ƛ (` zero)
```

We can replace the first variable by `ID`.

```
  _ : ƛ (` zero · ` zero) ↝ ƛ (ID · ` zero)
  _ = replace (ƛ (□ ·ₗ ` zero))
```
