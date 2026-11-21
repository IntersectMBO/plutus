---
title: Builtin.Value.Union.Properties
layout: page
---

This module proves that `merge∞` adds quantities token by token, and that `Value∞` is a
commutative group under `merge∞`, with `empty∞` as its identity and `negate∞` as
inverse.

```
module Builtin.Value.Union.Properties where
```

## Imports

```
open import Algebra.Structures using (IsCommutativeMonoid; IsAbelianGroup)
open import Data.List using (_∷_; [])
open import Data.List.Relation.Unary.Linked
  using (Linked; []; [-]; _∷_) renaming (tail to Linked-tail)
open import Data.Product using (_,_)
open import Data.Integer using (0ℤ)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; isEquivalence)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (recompute)

import Data.Integer as ℤ
import Data.Integer.Properties as ℤ

open import Builtin.Value.Base
open import Builtin.Value.Base.Properties
open import Builtin.Value.Union
```

## Lookup

The quantity of a token in the merge of two sorted association lists is the sum of its
quantities in each of them.

```
lookupEntry-merge
  : ∀ k kvs₁ kvs₂
  → Linked _<ᵉ_ kvs₁
  → Linked _<ᵉ_ kvs₂
  → lookupEntry k (mergeEntries kvs₁ kvs₂) ≡ lookupEntry k kvs₁ ℤ.+ lookupEntry k kvs₂
lookupEntry-merge-∷
  : ∀ k e₁ kvs₁ kvs₂
  → Linked _<ᵉ_ (e₁ ∷ kvs₁)
  → Linked _<ᵉ_ kvs₂
  → lookupEntry k (mergeEntries-∷ e₁ kvs₁ kvs₂)
    ≡ lookupEntry k (e₁ ∷ kvs₁) ℤ.+ lookupEntry k kvs₂

lookupEntry-merge k []          kvs₂ _  _  = sym (ℤ.+-identityˡ (lookupEntry k kvs₂))
lookupEntry-merge k (e₁ ∷ kvs₁) kvs₂ l₁ l₂ = lookupEntry-merge-∷ k e₁ kvs₁ kvs₂ l₁ l₂

lookupEntry-merge-∷ k e₁ kvs₁ [] _ _ = sym (ℤ.+-identityʳ (lookupEntry k (e₁ ∷ kvs₁)))
lookupEntry-merge-∷ k (k₁ , q₁) kvs₁ ((k₂ , q₂) ∷ kvs₂) l₁ l₂ with compareᵏ k₁ k₂
... | tri< k₁<k₂ _ _ with k₁ ≟ᵏ k
...   | yes refl =
  sym (trans (cong (λ x → q₁ ℤ.+ x) (lookupEntry-below k₁<k₂ l₂)) (ℤ.+-identityʳ q₁))
...   | no  _ = lookupEntry-merge k kvs₁ ((k₂ , q₂) ∷ kvs₂) (Linked-tail l₁) l₂
lookupEntry-merge-∷ k (k₁ , q₁) kvs₁ ((k₂ , q₂) ∷ kvs₂) l₁ l₂
    | tri> _ _ k₂<k₁ with k₂ ≟ᵏ k
...   | yes refl =
  sym (trans (cong (ℤ._+ q₂) (lookupEntry-below k₂<k₁ l₁)) (ℤ.+-identityˡ q₂))
...   | no  _ = lookupEntry-merge-∷ k (k₁ , q₁) kvs₁ kvs₂ l₁ (Linked-tail l₂)
lookupEntry-merge-∷ k (k₁ , q₁) kvs₁ ((k₁ , q₂) ∷ kvs₂) l₁ l₂
    | tri≈ _ refl _ with q₁ ℤ.+ q₂ ℤ.≟ 0ℤ
...   | yes q₁+q₂≡0 with k₁ ≟ᵏ k
...     | yes refl =
  trans (lookupEntry-merge k₁ kvs₁ kvs₂ (Linked-tail l₁) (Linked-tail l₂))
        (trans (cong₂ ℤ._+_ (lookupEntry-tail l₁) (lookupEntry-tail l₂))
               (sym q₁+q₂≡0))
...     | no  _ = lookupEntry-merge k kvs₁ kvs₂ (Linked-tail l₁) (Linked-tail l₂)
lookupEntry-merge-∷ k (k₁ , q₁) kvs₁ ((k₁ , q₂) ∷ kvs₂) l₁ l₂
    | tri≈ _ refl _ | no _ with k₁ ≟ᵏ k
...     | yes refl = refl
...     | no  _    = lookupEntry-merge k kvs₁ kvs₂ (Linked-tail l₁) (Linked-tail l₂)
```

For `Value∞`s, the sortedness of the association lists is irrelevant, but equality of
integers is decidable, so it can be recomputed.

```
lookup∞-merge∞
  : ∀ c t v₁ v₂
  → lookup∞ c t (merge∞ v₁ v₂) ≡ lookup∞ c t v₁ ℤ.+ lookup∞ c t v₂
lookup∞-merge∞ c t (mkValue∞ m₁ s₁ _) (mkValue∞ m₂ s₂ _) =
  recompute (_ ℤ.≟ _) (lookupEntry-merge (c , t) m₁ m₂ s₁ s₂)
```

## Algebra

Since a `Value∞` is determined by the quantities of its tokens, the laws of `merge∞` and
`negate∞` follow from those of the addition and negation of integers.

```
merge∞-comm : ∀ v₁ v₂ → merge∞ v₁ v₂ ≡ merge∞ v₂ v₁
merge∞-comm v₁ v₂ = lookup∞-injective λ c t →
  trans (lookup∞-merge∞ c t v₁ v₂)
        (trans (ℤ.+-comm (lookup∞ c t v₁) (lookup∞ c t v₂))
               (sym (lookup∞-merge∞ c t v₂ v₁)))

merge∞-assoc : ∀ v₁ v₂ v₃ → merge∞ (merge∞ v₁ v₂) v₃ ≡ merge∞ v₁ (merge∞ v₂ v₃)
merge∞-assoc v₁ v₂ v₃ = lookup∞-injective λ c t →
  trans (lookup∞-merge∞ c t (merge∞ v₁ v₂) v₃)
        (trans (cong (ℤ._+ lookup∞ c t v₃) (lookup∞-merge∞ c t v₁ v₂))
               (trans (ℤ.+-assoc (lookup∞ c t v₁) (lookup∞ c t v₂) (lookup∞ c t v₃))
                      (trans (cong (λ x → lookup∞ c t v₁ ℤ.+ x)
                                   (sym (lookup∞-merge∞ c t v₂ v₃)))
                             (sym (lookup∞-merge∞ c t v₁ (merge∞ v₂ v₃))))))

merge∞-identityˡ : ∀ v → merge∞ empty∞ v ≡ v
merge∞-identityˡ v = refl

merge∞-identityʳ : ∀ v → merge∞ v empty∞ ≡ v
merge∞-identityʳ v = trans (merge∞-comm v empty∞) (merge∞-identityˡ v)

merge∞-isCommutativeMonoid : IsCommutativeMonoid _≡_ merge∞ empty∞
merge∞-isCommutativeMonoid = record
  { isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = isEquivalence
        ; ∙-cong        = cong₂ merge∞
        }
      ; assoc = merge∞-assoc
      }
    ; identity = merge∞-identityˡ , merge∞-identityʳ
    }
  ; comm = merge∞-comm
  }

merge∞-inverseˡ : ∀ v → merge∞ (negate∞ v) v ≡ empty∞
merge∞-inverseˡ v = lookup∞-injective λ c t →
  trans (lookup∞-merge∞ c t (negate∞ v) v)
        (trans (cong (ℤ._+ lookup∞ c t v) (lookup∞-negate∞ c t v))
               (ℤ.+-inverseˡ (lookup∞ c t v)))

merge∞-inverseʳ : ∀ v → merge∞ v (negate∞ v) ≡ empty∞
merge∞-inverseʳ v = trans (merge∞-comm v (negate∞ v)) (merge∞-inverseˡ v)

merge∞-isAbelianGroup : IsAbelianGroup _≡_ merge∞ empty∞ negate∞
merge∞-isAbelianGroup = record
  { isGroup = record
    { isMonoid = IsCommutativeMonoid.isMonoid merge∞-isCommutativeMonoid
    ; inverse  = merge∞-inverseˡ , merge∞-inverseʳ
    ; ⁻¹-cong  = cong negate∞
    }
  ; comm = merge∞-comm
  }
```
