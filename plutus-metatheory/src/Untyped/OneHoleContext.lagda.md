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
open import Data.Nat
open import Data.List

private variable
  n m l : ℕ
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
```

## Plugging

Replace the hole by an (open) term.
```
plug : m ⊸ n ⊢ → m ⊢ → n ⊢
plug □ t = t
plug (ƛ C) t = ƛ (plug C t)
plug (C ·ₗ u) t = plug C t · u
plug (u ·ᵣ C) t = u · plug C t
plug (force C) t = force (plug C t)
plug (delay C) t = delay (plug C t)
plug (constr i xs C ys) t = constr i (xs ++ (plug C t ∷ ys))
plug (caseₗ C xs) t = case (plug C t) xs
plug (caseᵣ u xs C ys) t = case u (xs ++ (plug C t ∷ ys))
```

## Composition of contexts

For two contexts, `C ∘ D` is the context obtained by plugging `D` into `C`.

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
