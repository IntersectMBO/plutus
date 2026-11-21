---
title: Builtin.Value.Base.Properties
layout: page
---

This module proves that a `Value∞` is determined by the quantities of its tokens, as
given by `lookup∞`, and how negation affects them.

```
module Builtin.Value.Base.Properties where
```

## Imports

```
open import Data.Empty using (⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Linked
  using (Linked; []; [-]; _∷_) renaming (tail to Linked-tail)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Integer using (0ℤ)
open import Relation.Binary.Definitions using (DecidableEquality; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong₂)
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (recompute)

import Data.Integer as ℤ
import Data.List.Properties as List
import Data.List.Relation.Unary.All as All
import Data.Product.Properties as Product

open import Builtin.Value.Base
```

## The order on keys

```
<ᵏ-irrefl : ∀ {k} → ¬ (k <ᵏ k)
<ᵏ-irrefl = IsStrictTotalOrder.irrefl <ᵏ-isStrictTotalOrder (refl , refl)

<ᵏ-trans : ∀ {k₁ k₂ k₃} → k₁ <ᵏ k₂ → k₂ <ᵏ k₃ → k₁ <ᵏ k₃
<ᵏ-trans = IsStrictTotalOrder.trans <ᵏ-isStrictTotalOrder
```

In a sorted list, the key of the first entry is smaller than the keys of all the others.

```
head-< : ∀ {e kvs} → Linked _<ᵉ_ (e ∷ kvs) → All (λ e' → proj₁ e <ᵏ proj₁ e') kvs
head-< [-]       = []
head-< (r ∷ [-]) = r ∷ []
head-< {e} {e' ∷ e'' ∷ _} (r ∷ r' ∷ l) =
  r ∷ head-< {e} (<ᵏ-trans {proj₁ e} {proj₁ e'} {proj₁ e''} r r' ∷ l)
```

## Lookup

`lookupEntry k` is the quantity of the first entry with key `k`, or zero.

```
lookupEntry-here : ∀ k q kvs → lookupEntry k ((k , q) ∷ kvs) ≡ q
lookupEntry-here k q kvs with k ≟ᵏ k
... | yes _   = refl
... | no  k≢k = ⊥-elim (k≢k refl)

lookupEntry-< : ∀ k kvs → All (λ e → k <ᵏ proj₁ e) kvs → lookupEntry k kvs ≡ 0ℤ
lookupEntry-< k []               []         = refl
lookupEntry-< k ((k' , q) ∷ kvs) (k<k' ∷ a) with k' ≟ᵏ k
... | yes refl = ⊥-elim (<ᵏ-irrefl k<k')
... | no  _    = lookupEntry-< k kvs a

-- A key smaller than the first key of a sorted list is not in it.
lookupEntry-below
  : ∀ {k e kvs} → k <ᵏ proj₁ e → Linked _<ᵉ_ (e ∷ kvs) → lookupEntry k (e ∷ kvs) ≡ 0ℤ
lookupEntry-below {k} {e} {kvs} k<e l =
  lookupEntry-< k (e ∷ kvs) (k<e ∷ All.map (<ᵏ-trans k<e) (head-< l))

-- The first key of a sorted list is not in its tail.
lookupEntry-tail
  : ∀ {e kvs} → Linked _<ᵉ_ (e ∷ kvs) → lookupEntry (proj₁ e) kvs ≡ 0ℤ
lookupEntry-tail {e} {kvs} l = lookupEntry-< (proj₁ e) kvs (head-< l)
```

## Negation

Negating a value negates the quantity of every token.

```
lookupEntry-negate : ∀ k kvs → lookupEntry k (negateEntries kvs) ≡ ℤ.- lookupEntry k kvs
lookupEntry-negate k []               = refl
lookupEntry-negate k ((k' , q) ∷ kvs) with k' ≟ᵏ k
... | yes _ = refl
... | no  _ = lookupEntry-negate k kvs

lookup∞-negate∞ : ∀ c t v → lookup∞ c t (negate∞ v) ≡ ℤ.- lookup∞ c t v
lookup∞-negate∞ c t v = lookupEntry-negate (c , t) (Value∞.map v)
```

## Extensionality

Two well-formed association lists with the same quantity at every key are equal: at the
smaller of their first keys, one of them has a non-zero quantity and the other has none
unless the keys are equal, in which case the quantities are equal too, and so are the
tails.

```
NonZero : List Entry → Set
NonZero = All (λ e → proj₂ e ≢ 0ℤ)

lookupEntry-injective
  : ∀ kvs₁ kvs₂
  → Linked _<ᵉ_ kvs₁ → Linked _<ᵉ_ kvs₂
  → NonZero kvs₁ → NonZero kvs₂
  → (∀ k → lookupEntry k kvs₁ ≡ lookupEntry k kvs₂)
  → kvs₁ ≡ kvs₂
lookupEntry-injective [] [] _ _ _ _ _ = refl
lookupEntry-injective [] ((k , q) ∷ kvs) _ _ _ (nz ∷ _) eq =
  ⊥-elim (nz (sym (trans (eq k) (lookupEntry-here k q kvs))))
lookupEntry-injective ((k , q) ∷ kvs) [] _ _ (nz ∷ _) _ eq =
  ⊥-elim (nz (trans (sym (lookupEntry-here k q kvs)) (eq k)))
lookupEntry-injective ((k₁ , q₁) ∷ kvs₁) ((k₂ , q₂) ∷ kvs₂) l₁ l₂ (nz₁ ∷ z₁) (nz₂ ∷ z₂) eq
  with compareᵏ k₁ k₂
... | tri< k₁<k₂ _ _ =
  ⊥-elim (nz₁ (trans (sym (lookupEntry-here k₁ q₁ kvs₁))
                     (trans (eq k₁) (lookupEntry-below k₁<k₂ l₂))))
... | tri> _ _ k₂<k₁ =
  ⊥-elim (nz₂ (trans (sym (lookupEntry-here k₂ q₂ kvs₂))
                     (trans (sym (eq k₂)) (lookupEntry-below k₂<k₁ l₁))))
... | tri≈ _ refl _ =
  cong₂ (λ q kvs → (k₁ , q) ∷ kvs)
    (trans (sym (lookupEntry-here k₁ q₁ kvs₁))
           (trans (eq k₁) (lookupEntry-here k₁ q₂ kvs₂)))
    (lookupEntry-injective kvs₁ kvs₂ (Linked-tail l₁) (Linked-tail l₂) z₁ z₂ eq-tail)
  where
    eq-tail : ∀ k → lookupEntry k kvs₁ ≡ lookupEntry k kvs₂
    eq-tail k with k₁ ≟ᵏ k | eq k
    ... | yes refl | _ = trans (lookupEntry-tail l₁) (sym (lookupEntry-tail l₂))
    ... | no  _    | e = e
```

The invariants of a `Value∞` are irrelevant, so they can only be used to prove another
irrelevant statement. Equality of association lists is decidable, though, so it can be
recomputed from an irrelevant proof of it. Two `Value∞`s with equal association lists
are equal, as their other fields are irrelevant.

```
_≟ᵉ_ : DecidableEquality Entry
_≟ᵉ_ = Product.≡-dec _≟ᵏ_ ℤ._≟_

lookup∞-injective
  : ∀ {v₁ v₂} → (∀ c t → lookup∞ c t v₁ ≡ lookup∞ c t v₂) → v₁ ≡ v₂
lookup∞-injective {mkValue∞ m₁ s₁ z₁} {mkValue∞ m₂ s₂ z₂} eq
  with recompute (List.≡-dec _≟ᵉ_ m₁ m₂)
         (lookupEntry-injective m₁ m₂ s₁ s₂ z₁ z₂ (λ (c , t) → eq c t))
... | refl = refl
```
