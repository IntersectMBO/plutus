---
title: Builtin.Value.Union
layout: page
---

This module defines the pointwise sum of values, `merge∞`. Since `Value∞` places no
bound on quantities, `merge∞` is total. The union of the builtin values, which can fail,
is defined from it in `Builtin.Value`.

```
module Builtin.Value.Union where
```

## Imports

```
open import Data.List using (List; _∷_; [])
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Linked
  using (Linked; []; [-]; _∷_) renaming (tail to Linked-tail)
open import Data.Product using (_,_)
open import Data.Integer using (0ℤ)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Nullary using (yes; no)

import Data.Integer as ℤ

open import Builtin.Value.Base
```

## Merging association lists

`mergeEntries kvs₁ kvs₂` adds two sorted association lists pointwise: an entry whose key
is in only one of them is kept, and the entries of a key in both are replaced by a
single entry with the sum of their quantities, or dropped if that sum is zero.

```
mergeEntries   : List Entry → List Entry → List Entry
mergeEntries-∷ : Entry → List Entry → List Entry → List Entry

mergeEntries []         kvs₂ = kvs₂
mergeEntries (e ∷ kvs₁) kvs₂ = mergeEntries-∷ e kvs₁ kvs₂

mergeEntries-∷ e         kvs₁ []                 = e ∷ kvs₁
mergeEntries-∷ (k₁ , q₁) kvs₁ ((k₂ , q₂) ∷ kvs₂) with compareᵏ k₁ k₂
... | tri< _ _ _ = (k₁ , q₁) ∷ mergeEntries kvs₁ ((k₂ , q₂) ∷ kvs₂)
... | tri> _ _ _ = (k₂ , q₂) ∷ mergeEntries-∷ (k₁ , q₁) kvs₁ kvs₂
... | tri≈ _ _ _ with q₁ ℤ.+ q₂ ℤ.≟ 0ℤ
...   | yes _ = mergeEntries kvs₁ kvs₂
...   | no  _ = (k₁ , q₁ ℤ.+ q₂) ∷ mergeEntries kvs₁ kvs₂
```

## Merging keeps values well-formed

`mergeEntries` keeps the keys sorted. A property of all entries holds of the result if it
holds of both inputs and is preserved by adding the quantities of entries with the same
key, when the sum is non-zero.

```
private
  -- Merging lists with a lower bound `e` keeps that bound.
  mergeEntries-linked-∷
    : ∀ e kvs₁ kvs₂
    → Linked _<ᵉ_ (e ∷ kvs₁)
    → Linked _<ᵉ_ (e ∷ kvs₂)
    → Linked _<ᵉ_ (e ∷ mergeEntries kvs₁ kvs₂)
  mergeEntries-∷-linked-∷
    : ∀ e e₁ kvs₁ kvs₂
    → Linked _<ᵉ_ (e ∷ e₁ ∷ kvs₁)
    → Linked _<ᵉ_ (e ∷ kvs₂)
    → Linked _<ᵉ_ (e ∷ mergeEntries-∷ e₁ kvs₁ kvs₂)

  mergeEntries-linked-∷ e []          kvs₂ _  l₂ = l₂
  mergeEntries-linked-∷ e (e₁ ∷ kvs₁) kvs₂ l₁ l₂ =
    mergeEntries-∷-linked-∷ e e₁ kvs₁ kvs₂ l₁ l₂

  mergeEntries-∷-linked-∷ e e₁ kvs₁ [] l₁ _ = l₁
  mergeEntries-∷-linked-∷ e (k₁ , q₁) kvs₁ ((k₂ , q₂) ∷ kvs₂) (r₁ ∷ l₁) (r₂ ∷ l₂)
    with compareᵏ k₁ k₂
  ... | tri< k₁<k₂ _ _ =
    r₁ ∷ mergeEntries-linked-∷ (k₁ , q₁) kvs₁ ((k₂ , q₂) ∷ kvs₂) l₁ (k₁<k₂ ∷ l₂)
  ... | tri> _ _ k₂<k₁ =
    r₂ ∷ mergeEntries-∷-linked-∷ (k₂ , q₂) (k₁ , q₁) kvs₁ kvs₂ (k₂<k₁ ∷ l₁) l₂
  ... | tri≈ _ refl _ with q₁ ℤ.+ q₂ ℤ.≟ 0ℤ
  ...   | yes _ =
    mergeEntries-linked-∷ e kvs₁ kvs₂ (drop-second (r₁ ∷ l₁)) (drop-second (r₂ ∷ l₂))
    where
      drop-second : ∀ {e e' kvs} → Linked _<ᵉ_ (e ∷ e' ∷ kvs) → Linked _<ᵉ_ (e ∷ kvs)
      drop-second (_ ∷ [-])                       = [-]
      drop-second {e} {e'} {e'' ∷ _} (r ∷ r' ∷ l) = <ᵉ-trans {e} {e'} {e''} r r' ∷ l
  ...   | no  _ =
    r₁ ∷ mergeEntries-linked-∷ (k₁ , q₁ ℤ.+ q₂) kvs₁ kvs₂
           (replace-head l₁) (replace-head l₂)

  mergeEntries-∷-linked
    : ∀ e₁ kvs₁ kvs₂
    → Linked _<ᵉ_ (e₁ ∷ kvs₁)
    → Linked _<ᵉ_ kvs₂
    → Linked _<ᵉ_ (mergeEntries-∷ e₁ kvs₁ kvs₂)

mergeEntries-linked
  : ∀ kvs₁ kvs₂
  → Linked _<ᵉ_ kvs₁
  → Linked _<ᵉ_ kvs₂
  → Linked _<ᵉ_ (mergeEntries kvs₁ kvs₂)
mergeEntries-linked []          kvs₂ _  l₂ = l₂
mergeEntries-linked (e₁ ∷ kvs₁) kvs₂ l₁ l₂ = mergeEntries-∷-linked e₁ kvs₁ kvs₂ l₁ l₂

mergeEntries-∷-linked e₁ kvs₁ [] l₁ _ = l₁
mergeEntries-∷-linked (k₁ , q₁) kvs₁ ((k₂ , q₂) ∷ kvs₂) l₁ l₂ with compareᵏ k₁ k₂
... | tri< k₁<k₂ _ _ =
  mergeEntries-linked-∷ (k₁ , q₁) kvs₁ ((k₂ , q₂) ∷ kvs₂) l₁ (k₁<k₂ ∷ l₂)
... | tri> _ _ k₂<k₁ =
  mergeEntries-∷-linked-∷ (k₂ , q₂) (k₁ , q₁) kvs₁ kvs₂ (k₂<k₁ ∷ l₁) l₂
... | tri≈ _ refl _ with q₁ ℤ.+ q₂ ℤ.≟ 0ℤ
...   | yes _ = mergeEntries-linked kvs₁ kvs₂ (Linked-tail l₁) (Linked-tail l₂)
...   | no  _ =
  mergeEntries-linked-∷ (k₁ , q₁ ℤ.+ q₂) kvs₁ kvs₂ (replace-head l₁) (replace-head l₂)

-- Adding the quantities of two entries with the same key preserves `P`, when the sum is
-- non-zero.
+-Preserves : (Entry → Set) → Set
+-Preserves P =
  ∀ {k q₁ q₂} → P (k , q₁) → P (k , q₂) → q₁ ℤ.+ q₂ ≢ 0ℤ → P (k , q₁ ℤ.+ q₂)

mergeEntries-all
  : ∀ {P} → +-Preserves P
  → ∀ kvs₁ kvs₂ → All P kvs₁ → All P kvs₂ → All P (mergeEntries kvs₁ kvs₂)
private
  mergeEntries-∷-all
    : ∀ {P} → +-Preserves P
    → ∀ e₁ kvs₁ kvs₂
    → All P (e₁ ∷ kvs₁)
    → All P kvs₂
    → All P (mergeEntries-∷ e₁ kvs₁ kvs₂)

mergeEntries-all +-P []          kvs₂ _  a₂ = a₂
mergeEntries-all +-P (e₁ ∷ kvs₁) kvs₂ a₁ a₂ = mergeEntries-∷-all +-P e₁ kvs₁ kvs₂ a₁ a₂

mergeEntries-∷-all +-P e₁ kvs₁ [] a₁ _ = a₁
mergeEntries-∷-all +-P (k₁ , q₁) kvs₁ ((k₂ , q₂) ∷ kvs₂) (p₁ ∷ a₁) (p₂ ∷ a₂)
  with compareᵏ k₁ k₂
... | tri< _ _ _ = p₁ ∷ mergeEntries-all +-P kvs₁ ((k₂ , q₂) ∷ kvs₂) a₁ (p₂ ∷ a₂)
... | tri> _ _ _ = p₂ ∷ mergeEntries-∷-all +-P (k₁ , q₁) kvs₁ kvs₂ (p₁ ∷ a₁) a₂
... | tri≈ _ refl _ with q₁ ℤ.+ q₂ ℤ.≟ 0ℤ
...   | yes _  = mergeEntries-all +-P kvs₁ kvs₂ a₁ a₂
...   | no  nz = +-P p₁ p₂ nz ∷ mergeEntries-all +-P kvs₁ kvs₂ a₁ a₂
```

## Merging values

`merge∞ v₁ v₂` adds the quantities of `v₁` and `v₂` token by token.

```
merge∞ : Value∞ → Value∞ → Value∞
merge∞ (mkValue∞ m₁ s₁ z₁) (mkValue∞ m₂ s₂ z₂) =
  mkValue∞
    (mergeEntries m₁ m₂)
    (mergeEntries-linked m₁ m₂ s₁ s₂)
    (mergeEntries-all (λ _ _ nz → nz) m₁ m₂ z₁ z₂)
```
