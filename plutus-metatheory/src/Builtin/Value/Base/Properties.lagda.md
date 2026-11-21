---
title: Builtin.Value.Base.Properties
layout: page
---

This module proves that a `Value∞` is determined by the quantities of its tokens, as
given by `lookup∞`, how negation and scaling affect them, and that `contains∞` compares
them.

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
open import Data.Bool using (T)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Integer using (0ℤ; 1ℤ)
open import Relation.Binary.Definitions using (DecidableEquality; tri<; tri≈; tri>)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (recompute; toWitness; fromWitness)

import Data.Integer as ℤ
import Data.Integer.Properties as ℤ
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

## Scaling

Scaling a value scales the quantity of every token.

```
lookupEntry-scale
  : ∀ n k kvs → lookupEntry k (scaleEntries n kvs) ≡ n ℤ.* lookupEntry k kvs
lookupEntry-scale n k []               = sym (ℤ.*-zeroʳ n)
lookupEntry-scale n k ((k' , q) ∷ kvs) with k' ≟ᵏ k
... | yes _ = refl
... | no  _ = lookupEntry-scale n k kvs

lookup∞-scale∞ : ∀ n c t v → lookup∞ c t (scale∞ n v) ≡ n ℤ.* lookup∞ c t v
lookup∞-scale∞ n c t (mkValue∞ m _ _) with n ℤ.≟ 0ℤ
... | yes refl = refl
... | no  _    = lookupEntry-scale n (c , t) m
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

## Algebra of scaling

Since a `Value∞` is determined by the quantities of its tokens, the laws of scaling
follow from those of the multiplication of integers. Negation is scaling by `-1`.

```
scale∞-zero : ∀ v → scale∞ 0ℤ v ≡ empty∞
scale∞-zero v = lookup∞-injective λ c t → lookup∞-scale∞ 0ℤ c t v

scale∞-identity : ∀ v → scale∞ 1ℤ v ≡ v
scale∞-identity v =
  lookup∞-injective λ c t → trans (lookup∞-scale∞ 1ℤ c t v) (ℤ.*-identityˡ _)

scale∞-assoc : ∀ m n v → scale∞ (m ℤ.* n) v ≡ scale∞ m (scale∞ n v)
scale∞-assoc m n v = lookup∞-injective λ c t →
  trans (lookup∞-scale∞ (m ℤ.* n) c t v)
    (trans (ℤ.*-assoc m n _)
      (sym (trans (lookup∞-scale∞ m c t (scale∞ n v))
                  (cong (m ℤ.*_) (lookup∞-scale∞ n c t v)))))

negate∞≡scale∞-1 : ∀ v → negate∞ v ≡ scale∞ ℤ.-1ℤ v
negate∞≡scale∞-1 v = lookup∞-injective λ c t →
  trans (lookup∞-negate∞ c t v)
    (sym (trans (lookup∞-scale∞ ℤ.-1ℤ c t v) (ℤ.-1*i≡-i _)))
```

## Containment

The quantities of a value with non-negative quantities are non-negative, including those
of absent tokens.

```
lookupEntry-nonNegative
  : ∀ k kvs → All (λ e → 0ℤ ℤ.≤ proj₂ e) kvs → 0ℤ ℤ.≤ lookupEntry k kvs
lookupEntry-nonNegative k []               []      = ℤ.≤-refl
lookupEntry-nonNegative k ((k' , q) ∷ kvs) (p ∷ a) with k' ≟ᵏ k
... | yes _ = p
... | no  _ = lookupEntry-nonNegative k kvs a
```

`v₁` contains `v₂` exactly when every token has at least the same quantity in `v₁` as in
`v₂`, if the quantities of `v₁` are non-negative. Tokens absent from `v₂` have quantity
zero in it, so they need the quantities of `v₁` to be non-negative. Conversely, the
quantity of the first token of `v₂` is its quantity in `v₂`, and the token is not in the
rest of `v₂`, as `v₂` is sorted.

```
Contains∞ : Value∞ → Value∞ → Set
Contains∞ v₁ v₂ = ∀ c t → lookup∞ c t v₂ ℤ.≤ lookup∞ c t v₁

containsEntries⇒≤
  : ∀ kvs₁ kvs₂
  → All (λ e → 0ℤ ℤ.≤ proj₂ e) kvs₁
  → ContainsEntries kvs₁ kvs₂
  → ∀ k → lookupEntry k kvs₂ ℤ.≤ lookupEntry k kvs₁
containsEntries⇒≤ kvs₁ []                n []      k = lookupEntry-nonNegative k kvs₁ n
containsEntries⇒≤ kvs₁ ((k' , q) ∷ kvs₂) n (p ∷ a) k with k' ≟ᵏ k
... | yes refl = p
... | no  _    = containsEntries⇒≤ kvs₁ kvs₂ n a k

≤⇒containsEntries
  : ∀ kvs₁ kvs₂
  → All (λ e → 0ℤ ℤ.≤ proj₂ e) kvs₁
  → Linked _<ᵉ_ kvs₂
  → (∀ k → lookupEntry k kvs₂ ℤ.≤ lookupEntry k kvs₁)
  → ContainsEntries kvs₁ kvs₂
≤⇒containsEntries kvs₁ []               _ _ _  = []
≤⇒containsEntries kvs₁ ((k , q) ∷ kvs₂) n l le =
  q≤ ∷ ≤⇒containsEntries kvs₁ kvs₂ n (Linked-tail l) le-tail
  where
    q≤ : q ℤ.≤ lookupEntry k kvs₁
    q≤ = subst (ℤ._≤ lookupEntry k kvs₁) (lookupEntry-here k q kvs₂) (le k)

    le-tail : ∀ k' → lookupEntry k' kvs₂ ℤ.≤ lookupEntry k' kvs₁
    le-tail k' with k ≟ᵏ k' | le k'
    ... | yes refl | _ =
      subst (ℤ._≤ lookupEntry k kvs₁) (sym (lookupEntry-tail l))
        (lookupEntry-nonNegative k kvs₁ n)
    ... | no  _    | le' = le'
```

The sortedness of `v₂` is irrelevant, but `ContainsEntries` is decidable, so it can be
recomputed.

```
contains∞-correct
  : ∀ v₁ v₂ → NonNegative v₁ → T (contains∞ v₁ v₂) ⇔ Contains∞ v₁ v₂
contains∞-correct (mkValue∞ m₁ _ _) (mkValue∞ m₂ s₂ _) n = mk⇔
  (λ c c' t → containsEntries⇒≤ m₁ m₂ n (toWitness {a? = m₁ ⊇? m₂} c) (c' , t))
  (λ le → fromWitness {a? = m₁ ⊇? m₂}
            (recompute (m₁ ⊇? m₂) (≤⇒containsEntries m₁ m₂ n s₂ (λ (c , t) → le c t))))
  where
    _⊇?_ = containsEntries?
```
