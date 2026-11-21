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
open import Data.Product using (_,_; proj₁)
open import Data.Integer using (0ℤ; 1ℤ)
open import Relation.Binary.Definitions using (DecidableEquality; tri<; tri≈; tri>)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
open import Relation.Binary.Structures using (IsStrictTotalOrder)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (recompute; toWitness; fromWitness)

import Data.Integer as ℤ
import Relation.Unary as U
import Data.Integer.Properties as ℤ
import Data.List.Properties as List
import Data.List.Relation.Unary.All as All
import Data.Product.Properties as Product

open import Builtin.Value.Base
open import Data.List.Membership.Propositional using (_∈_; _∉_)
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

In particular, negating a value negates the quantity of every token.

```
lookup∞-negate∞ : ∀ c t v → lookup∞ c t (negate∞ v) ≡ ℤ.- lookup∞ c t v
lookup∞-negate∞ c t v = trans (lookup∞-scale∞ ℤ.-1ℤ c t v) (ℤ.-1*i≡-i _)
```

## Filtering

Filtering keeps the quantity of the tokens that satisfy the property, and removes the
others.

```
lookupEntry-filter-yes
  : ∀ {P : Key → Set} (P? : U.Decidable P) {k} kvs
  → P k → lookupEntry k (filterEntries P? kvs) ≡ lookupEntry k kvs
lookupEntry-filter-yes P? []               _  = refl
lookupEntry-filter-yes P? {k} ((k' , q) ∷ kvs) pk with P? k'
... | yes _ with k' ≟ᵏ k
...   | yes _ = refl
...   | no  _ = lookupEntry-filter-yes P? kvs pk
lookupEntry-filter-yes P? {k} ((k' , q) ∷ kvs) pk | no ¬pk' with k' ≟ᵏ k
...   | yes refl = ⊥-elim (¬pk' pk)
...   | no  _    = lookupEntry-filter-yes P? kvs pk

lookupEntry-filter-no
  : ∀ {P : Key → Set} (P? : U.Decidable P) {k} kvs
  → ¬ P k → lookupEntry k (filterEntries P? kvs) ≡ 0ℤ
lookupEntry-filter-no P? []               _   = refl
lookupEntry-filter-no P? {k} ((k' , q) ∷ kvs) ¬pk with P? k'
... | no  _ = lookupEntry-filter-no P? kvs ¬pk
... | yes pk' with k' ≟ᵏ k
...   | yes refl = ⊥-elim (¬pk pk')
...   | no  _    = lookupEntry-filter-no P? kvs ¬pk

lookup∞-filter∞-yes
  : ∀ {P : Key → Set} (P? : U.Decidable P) {c t} v
  → P (c , t) → lookup∞ c t (filter∞ P? v) ≡ lookup∞ c t v
lookup∞-filter∞-yes P? v = lookupEntry-filter-yes P? (Value∞.map v)

lookup∞-filter∞-no
  : ∀ {P : Key → Set} (P? : U.Decidable P) {c t} v
  → ¬ P (c , t) → lookup∞ c t (filter∞ P? v) ≡ 0ℤ
lookup∞-filter∞-no P? v = lookupEntry-filter-no P? (Value∞.map v)
```

So `delete∞ c t` removes the token `t` of the currency `c`, and keeps the others.

```
lookup∞-delete∞-≡ : ∀ c t v → lookup∞ c t (delete∞ c t v) ≡ 0ℤ
lookup∞-delete∞-≡ c t v = lookup∞-filter∞-no _ v λ k≢k → k≢k refl

lookup∞-delete∞-≢
  : ∀ {c t} c' t' v
  → (c' , t') ≢ (c , t) → lookup∞ c' t' (delete∞ c t v) ≡ lookup∞ c' t' v
lookup∞-delete∞-≢ c' t' v = lookup∞-filter∞-yes _ v
```

Also, `keepPolicies∞ ps` keeps exactly the tokens of the currencies in `ps`, and
`dropPolicies∞ ps` the others.

```
lookup∞-keepPolicies∞-∈
  : ∀ {c} ps t v → c ∈ ps → lookup∞ c t (keepPolicies∞ ps v) ≡ lookup∞ c t v
lookup∞-keepPolicies∞-∈ ps t v = lookup∞-filter∞-yes _ v

lookup∞-keepPolicies∞-∉
  : ∀ {c} ps t v → c ∉ ps → lookup∞ c t (keepPolicies∞ ps v) ≡ 0ℤ
lookup∞-keepPolicies∞-∉ ps t v = lookup∞-filter∞-no _ v

lookup∞-dropPolicies∞-∈
  : ∀ {c} ps t v → c ∈ ps → lookup∞ c t (dropPolicies∞ ps v) ≡ 0ℤ
lookup∞-dropPolicies∞-∈ ps t v c∈ps = lookup∞-filter∞-no _ v (λ c∉ps → c∉ps c∈ps)

lookup∞-dropPolicies∞-∉
  : ∀ {c} ps t v → c ∉ ps → lookup∞ c t (dropPolicies∞ ps v) ≡ lookup∞ c t v
lookup∞-dropPolicies∞-∉ ps t v = lookup∞-filter∞-yes _ v
```

## Extensionality

Two well-formed association lists with the same quantity at every key are equal: at the
smaller of their first keys, one of them has a non-zero quantity and the other has none
unless the keys are equal, in which case the quantities are equal too, and so are the
tails.

```
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
follow from those of the multiplication of integers.

```
scale∞-zero : ∀ v → scale∞ 0ℤ v ≡ empty∞
scale∞-zero v = lookup∞-injective λ c t → lookup∞-scale∞ 0ℤ c t v

scale∞-identity : ∀ v → scale∞ 1ℤ v ≡ v
scale∞-identity v =
  lookup∞-injective λ c t → trans (lookup∞-scale∞ 1ℤ c t v) (ℤ.*-identityˡ _)

scale∞-assoc : ∀ m n v → scale∞ (m ℤ.* n) v ≡ scale∞ m (scale∞ n v)
scale∞-assoc m n v = lookup∞-injective λ c t → let q = lookup∞ c t in begin
  q (scale∞ (m ℤ.* n) v)    ≡⟨ lookup∞-scale∞ (m ℤ.* n) c t v ⟩
  (m ℤ.* n) ℤ.* q v         ≡⟨ ℤ.*-assoc m n (q v) ⟩
  m ℤ.* (n ℤ.* q v)         ≡⟨ cong (m ℤ.*_) (lookup∞-scale∞ n c t v) ⟨
  m ℤ.* q (scale∞ n v)      ≡⟨ lookup∞-scale∞ m c t (scale∞ n v) ⟨
  q (scale∞ m (scale∞ n v)) ∎
  where open ≡-Reasoning
```

## Containment

The quantities of a value with non-negative quantities are non-negative, including those
of absent tokens.

```
lookupEntry-nonNegative : ∀ k kvs → NonNegative kvs → 0ℤ ℤ.≤ lookupEntry k kvs
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
  → NonNegative kvs₁
  → ContainsEntries kvs₁ kvs₂
  → ∀ k → lookupEntry k kvs₂ ℤ.≤ lookupEntry k kvs₁
containsEntries⇒≤ kvs₁ []                n []      k = lookupEntry-nonNegative k kvs₁ n
containsEntries⇒≤ kvs₁ ((k' , q) ∷ kvs₂) n (p ∷ a) k with k' ≟ᵏ k
... | yes refl = p
... | no  _    = containsEntries⇒≤ kvs₁ kvs₂ n a k

≤⇒containsEntries
  : ∀ kvs₁ kvs₂
  → NonNegative kvs₁
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
  : ∀ v₁ v₂ → NonNegative (Value∞.map v₁) → T (contains∞ v₁ v₂) ⇔ Contains∞ v₁ v₂
contains∞-correct (mkValue∞ m₁ _ _) (mkValue∞ m₂ s₂ _) n = mk⇔
  (λ c c' t → containsEntries⇒≤ m₁ m₂ n (toWitness {a? = m₁ ⊇? m₂} c) (c' , t))
  (λ le → fromWitness {a? = m₁ ⊇? m₂}
            (recompute (m₁ ⊇? m₂) (≤⇒containsEntries m₁ m₂ n s₂ (λ (c , t) → le c t))))
  where
    _⊇?_ = containsEntries?
```
