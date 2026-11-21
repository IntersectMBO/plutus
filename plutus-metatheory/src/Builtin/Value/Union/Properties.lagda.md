---
title: Builtin.Value.Union.Properties
layout: page
---

This module proves that `merge∞` adds quantities token by token, and that `Value∞` is a
commutative group under `merge∞`, with `empty∞` as its identity and `negate∞` as
inverse. With `scale∞`, it is a module over the integers.

```
module Builtin.Value.Union.Properties where
```

## Imports

```
open import Algebra.Module.Structures using (IsLeftModule)
open import Algebra.Structures using (IsCommutativeMonoid; IsAbelianGroup)
open import Data.List using (_∷_; [])
open import Data.List.Relation.Unary.Linked
  using (Linked; []; [-]; _∷_) renaming (tail to Linked-tail)
open import Data.Product using (_,_)
open import Data.Integer using (0ℤ)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; isEquivalence)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)
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
`negate∞` follow from those of the addition and negation of integers. In the proofs,
`q v` is the quantity of the token under consideration in `v`.

```
open ≡-Reasoning

merge∞-comm : ∀ v₁ v₂ → merge∞ v₁ v₂ ≡ merge∞ v₂ v₁
merge∞-comm v₁ v₂ = lookup∞-injective λ c t → let q = lookup∞ c t in begin
  q (merge∞ v₁ v₂)  ≡⟨ lookup∞-merge∞ c t v₁ v₂ ⟩
  q v₁ ℤ.+ q v₂     ≡⟨ ℤ.+-comm (q v₁) (q v₂) ⟩
  q v₂ ℤ.+ q v₁     ≡⟨ lookup∞-merge∞ c t v₂ v₁ ⟨
  q (merge∞ v₂ v₁)  ∎

merge∞-assoc : ∀ v₁ v₂ v₃ → merge∞ (merge∞ v₁ v₂) v₃ ≡ merge∞ v₁ (merge∞ v₂ v₃)
merge∞-assoc v₁ v₂ v₃ = lookup∞-injective λ c t → let q = lookup∞ c t in begin
  q (merge∞ (merge∞ v₁ v₂) v₃)  ≡⟨ lookup∞-merge∞ c t (merge∞ v₁ v₂) v₃ ⟩
  q (merge∞ v₁ v₂) ℤ.+ q v₃     ≡⟨ cong (ℤ._+ q v₃) (lookup∞-merge∞ c t v₁ v₂) ⟩
  (q v₁ ℤ.+ q v₂) ℤ.+ q v₃      ≡⟨ ℤ.+-assoc (q v₁) (q v₂) (q v₃) ⟩
  q v₁ ℤ.+ (q v₂ ℤ.+ q v₃)      ≡⟨ cong (λ x → q v₁ ℤ.+ x) (lookup∞-merge∞ c t v₂ v₃) ⟨
  q v₁ ℤ.+ q (merge∞ v₂ v₃)     ≡⟨ lookup∞-merge∞ c t v₁ (merge∞ v₂ v₃) ⟨
  q (merge∞ v₁ (merge∞ v₂ v₃))  ∎

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
merge∞-inverseˡ v = lookup∞-injective λ c t → let q = lookup∞ c t in begin
  q (merge∞ (negate∞ v) v)  ≡⟨ lookup∞-merge∞ c t (negate∞ v) v ⟩
  q (negate∞ v) ℤ.+ q v     ≡⟨ cong (ℤ._+ q v) (lookup∞-negate∞ c t v) ⟩
  ℤ.- q v ℤ.+ q v           ≡⟨ ℤ.+-inverseˡ (q v) ⟩
  0ℤ                        ∎

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

## Scaling

Scaling distributes over `merge∞` and over the addition of integers, and scaling the
empty value gives the empty value. Together with the laws of
`Builtin.Value.Base.Properties`, this makes `Value∞` a module over the integers.

```
scale∞-zeroʳ : ∀ n → scale∞ n empty∞ ≡ empty∞
scale∞-zeroʳ n = lookup∞-injective λ c t →
  trans (lookup∞-scale∞ n c t empty∞) (ℤ.*-zeroʳ n)

scale∞-distribˡ
  : ∀ n v₁ v₂ → scale∞ n (merge∞ v₁ v₂) ≡ merge∞ (scale∞ n v₁) (scale∞ n v₂)
scale∞-distribˡ n v₁ v₂ = lookup∞-injective λ c t → let q = lookup∞ c t in begin
  q (scale∞ n (merge∞ v₁ v₂))
    ≡⟨ lookup∞-scale∞ n c t (merge∞ v₁ v₂) ⟩
  n ℤ.* q (merge∞ v₁ v₂)
    ≡⟨ cong (n ℤ.*_) (lookup∞-merge∞ c t v₁ v₂) ⟩
  n ℤ.* (q v₁ ℤ.+ q v₂)
    ≡⟨ ℤ.*-distribˡ-+ n (q v₁) (q v₂) ⟩
  n ℤ.* q v₁ ℤ.+ n ℤ.* q v₂
    ≡⟨ cong₂ ℤ._+_ (lookup∞-scale∞ n c t v₁) (lookup∞-scale∞ n c t v₂) ⟨
  q (scale∞ n v₁) ℤ.+ q (scale∞ n v₂)
    ≡⟨ lookup∞-merge∞ c t (scale∞ n v₁) (scale∞ n v₂) ⟨
  q (merge∞ (scale∞ n v₁) (scale∞ n v₂))
    ∎

scale∞-distribʳ
  : ∀ v m n → scale∞ (m ℤ.+ n) v ≡ merge∞ (scale∞ m v) (scale∞ n v)
scale∞-distribʳ v m n = lookup∞-injective λ c t → let q = lookup∞ c t in begin
  q (scale∞ (m ℤ.+ n) v)
    ≡⟨ lookup∞-scale∞ (m ℤ.+ n) c t v ⟩
  (m ℤ.+ n) ℤ.* q v
    ≡⟨ ℤ.*-distribʳ-+ (q v) m n ⟩
  m ℤ.* q v ℤ.+ n ℤ.* q v
    ≡⟨ cong₂ ℤ._+_ (lookup∞-scale∞ m c t v) (lookup∞-scale∞ n c t v) ⟨
  q (scale∞ m v) ℤ.+ q (scale∞ n v)
    ≡⟨ lookup∞-merge∞ c t (scale∞ m v) (scale∞ n v) ⟨
  q (merge∞ (scale∞ m v) (scale∞ n v))
    ∎

scale∞-isLeftModule : IsLeftModule ℤ.+-*-ring _≡_ merge∞ empty∞ negate∞ scale∞
scale∞-isLeftModule = record
  { isLeftSemimodule = record
    { +ᴹ-isCommutativeMonoid = merge∞-isCommutativeMonoid
    ; isPreleftSemimodule = record
      { *ₗ-cong      = cong₂ scale∞
      ; *ₗ-zeroˡ     = scale∞-zero
      ; *ₗ-distribʳ  = scale∞-distribʳ
      ; *ₗ-identityˡ = scale∞-identity
      ; *ₗ-assoc     = scale∞-assoc
      ; *ₗ-zeroʳ     = scale∞-zeroʳ
      ; *ₗ-distribˡ  = scale∞-distribˡ
      }
    }
  ; -ᴹ‿cong    = cong negate∞
  ; -ᴹ‿inverse = merge∞-inverseˡ , merge∞-inverseʳ
  }
```
