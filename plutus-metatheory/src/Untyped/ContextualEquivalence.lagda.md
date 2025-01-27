---
title: Contextual Equivalence
layout: page
---

```
module Untyped.ContextualEquivalence where
```

## Imports

```
open import Untyped using (_⊢; case; builtin; _·_; force; `; ƛ; delay; con; constr; error)
open import Untyped.RenamingSubstitution using (_[_])
open import Data.Maybe using (Maybe; just; nothing)
open import RawU using (TmCon)
open import Builtin using (Builtin;equals;decBuiltin)
open import Untyped.Reduction using (Value;_⟶_;_⟶*_;value-¬⟶ )
open import Data.Empty using (⊥;⊥-elim)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
```
## Contexts
```
variable
  X Y : Set

data _⊢-⇛_⊢ : Set → Set → Set₁ where
  □ : X ⊢-⇛ X ⊢
  ƛ□ : (𝒞 : X ⊢-⇛ (Maybe Y) ⊢)
     → X ⊢-⇛ Y ⊢
  _□·_ :
       (𝒞 : X ⊢-⇛ Y ⊢)
       (M : Y ⊢)
       → ------------------------
       X ⊢-⇛ Y ⊢
  _·□_ :
       (L : Y ⊢)
       (𝒞 : X ⊢-⇛ Y ⊢)
       → ------------------------
       X ⊢-⇛ Y ⊢

_⟨_⟩ : (X ⊢-⇛ Y ⊢) → X ⊢ → Y ⊢
□ ⟨ t ⟩ = t
(ƛ□ 𝒞)⟨ t ⟩ = ƛ (𝒞 ⟨ t ⟩)
(𝒞 □· M) ⟨ P ⟩ = (𝒞 ⟨ P ⟩) · M
(L ·□ 𝒞) ⟨ P ⟩ = L · (𝒞 ⟨ P ⟩)

```
Terminates
```
_⇓ : X ⊢ → Set
M ⇓ = ∃[ V ] ((Value V) × (M ⟶* V))
```
## Equivalence
```
_iff_ : Set → Set → Set
A iff B = (A → B) × (B → A)

_≃_ : X ⊢ → X ⊢ → Set₁
M ≃ N = ∀ (𝒞 : _ ⊢-⇛ ⊥ ⊢) → ((𝒞 ⟨ M ⟩) ⇓) iff ((𝒞 ⟨ N ⟩) ⇓)

```
## Properties
```
refl-≃ : ∀ (M : X ⊢) → M ≃ M
refl-≃ = λ M 𝒞 → (λ z → z) , (λ z → z)

tran-≃ : ∀ (L M N : X ⊢) → L ≃ M → M ≃ N → L ≃ N
tran-≃ L M N L≃M M≃N 𝒞 = ( (λ L⇓ → M≃N 𝒞 .proj₁ (L≃M 𝒞 .proj₁ L⇓)) , (λ N⇓ → L≃M 𝒞 .proj₂ (M≃N 𝒞 .proj₂ N⇓)) )

⟶-⇓ : ∀(M N : X ⊢) → M ⟶ N → M ⇓ → N ⇓
⟶-⇓ M N M⟶N (V , Vv , _⟶*_.refl) = ⊥-elim (value-¬⟶ Vv (N , M⟶N))
⟶-⇓ M N M⟶N (V , Vv , _⟶*_.trans M⟶P P⟶*V) = V , (Vv , _⟶*_.trans {!!} P⟶*V)

⟶*-≃ : ∀(M N : X ⊢) → M ⟶* N → M ≃ N
⟶*-≃ M N _⟶*_.refl = λ 𝒞 → (λ z → z) , (λ z → z)
⟶*-≃ M N (_⟶*_.trans x M⟶*N) = {!!}
```
## Example
```

```
