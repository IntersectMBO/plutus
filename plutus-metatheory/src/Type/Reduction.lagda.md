---
title: Type Reduction
layout: page
---

```
module Type.Reduction where
```

Right now this file is not used in other things. We compute types via
NBE. Instead, it acts as a warmup to understanding reduction of terms.

This version of reduction does not compute under binders. The NBE
version does full normalisation.

## Imports

```
open import Type
open import Type.RenamingSubstitution
open import Builtin.Constant.Type

open import Agda.Builtin.Nat
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)
```

## Values

```
data Value⋆ : ∀ {Γ K} → Γ ⊢⋆ K → Set where

  V-Π : ∀ {Φ K}
    → (N : Φ ,⋆ K ⊢⋆ *)
      ----------------------------
    → Value⋆ (Π N)

  _V-⇒_ : ∀ {Φ} {S : Φ ⊢⋆ *} {T : Φ ⊢⋆ *}
    → Value⋆ S
    → Value⋆ T
      -----------------------------------
    → Value⋆ (S ⇒ T)

  V-ƛ : ∀ {Φ K J}
    → (N : Φ ,⋆ K ⊢⋆ J)
      -----------------------------
    → Value⋆ (ƛ N)

  V-con : ∀{Φ}
    → (tcn : TyCon)
      ------------------
    → Value⋆ {Γ = Φ} (con tcn)

  V-μ : ∀ {Φ K}{S}{T : Φ ⊢⋆ K}
    → Value⋆ S
    → Value⋆ T
    ----------------------------
    → Value⋆ (μ S T)
```

## Intrinsically Kind Preserving Type Reduction

```
infix 2 _—→⋆_
infix 2 _—↠⋆_

data _—→⋆_ : ∀ {Γ J} → (Γ ⊢⋆ J) → (Γ ⊢⋆ J) → Set where
  ξ-⇒₁ : ∀ {Φ} {S S' : Φ ⊢⋆ *} {T : Φ ⊢⋆ *}
    → S —→⋆ S'
      -----------------------------------
    → S ⇒ T —→⋆ S' ⇒ T

  ξ-⇒₂ : ∀ {Φ} {S : Φ ⊢⋆ *} {T T' : Φ ⊢⋆ *}
    → Value⋆ S
    → T —→⋆ T'
      -----------------------------------
    → S ⇒ T —→⋆ S ⇒ T'

  ξ-·₁ : ∀ {Γ K J} {L L′ : Γ ⊢⋆ K ⇒ J} {M : Γ ⊢⋆ K}
    → L —→⋆ L′
      -----------------
    → L · M —→⋆ L′ · M

  ξ-·₂ : ∀ {Γ K J} {V : Γ ⊢⋆ K ⇒ J} {M M′ : Γ ⊢⋆ K}
    → Value⋆ V
    → M —→⋆ M′
      --------------
    → V · M —→⋆ V · M′

  β-ƛ : ∀ {Γ K J} {N : Γ ,⋆ K ⊢⋆ J} {W : Γ ⊢⋆ K}
    → Value⋆ W
      -------------------
    → ƛ N · W —→⋆ N [ W ]

  ξ-μ₁ : ∀ {Φ K} {S S'} {T : Φ ⊢⋆ K}
    → S —→⋆ S'
      ------------------------------
    → μ S T —→⋆ μ S' T

  ξ-μ₂ : ∀ {Φ K} {S} {T T' : Φ ⊢⋆ K}
    → Value⋆ S
    → T —→⋆ T'
      ------------------------------
    → μ S T —→⋆ μ S T'
```

```
data _—↠⋆_ {J Γ} :  (Γ ⊢⋆ J) → (Γ ⊢⋆ J) → Set where

  refl—↠⋆ : ∀{M}
      --------
    → M —↠⋆ M

  trans—↠⋆ : {L : Γ ⊢⋆ J} {M N : Γ ⊢⋆ J}
    → L —→⋆ M
    → M —↠⋆ N
      ---------
    → L —↠⋆ N
```

```
data Progress⋆ {Γ K} (M : Γ ⊢⋆ K) : Set where
  step : ∀ {N : Γ ⊢⋆ K}
    → M —→⋆ N
      -------------
    → Progress⋆ M
  done :
      Value⋆ M
      ----------
    → Progress⋆ M
```

```
progress⋆ : ∀ {K} → (M : ∅ ⊢⋆ K) → Progress⋆ M
progress⋆ (` ())
progress⋆ (μ M N) with progress⋆ M
... | step p  = step (ξ-μ₁ p)
... | done VM with progress⋆ N
... | step p  = step (ξ-μ₂ VM p)
... | done VN = done (V-μ VM VN)
progress⋆ (Π M)   = done (V-Π M)
progress⋆ (M ⇒ N) with progress⋆ M
... | step p = step (ξ-⇒₁ p)
... | done VM with progress⋆ N
... | step q  = step (ξ-⇒₂ VM q)
... | done VN = done (VM V-⇒ VN)
progress⋆ (ƛ M)   = done (V-ƛ M)
progress⋆ (M · N)  with progress⋆ M
... | step p = step (ξ-·₁ p)
... | done VM with progress⋆ N
... | step p = step (ξ-·₂ VM p)
progress⋆ (.(ƛ _) · N) | done (V-ƛ M) | done VN = step (β-ƛ VN)
progress⋆ (con tcn) = done (V-con tcn)
```

```
open import Relation.Nullary
open import Data.Product
open import Data.Empty

notboth : ∀{Φ K}(A : Φ ⊢⋆ K) → ¬ (Value⋆ A × (Σ (Φ ⊢⋆ K) (A —→⋆_)))
notboth .(_ ⇒ _) ((V V-⇒ W) , .(_ ⇒ _) , ξ-⇒₁ p)   = notboth _ (V , _ , p)
notboth .(_ ⇒ _) ((V V-⇒ W) , .(_ ⇒ _) , ξ-⇒₂ _ p) = notboth _ (W , _ , p)
notboth .(μ _ _) (V-μ V W   , .(μ _ _)  , ξ-μ₁ p)   = notboth _ (V , _ , p)
notboth .(μ _ _) (V-μ V W   , .(μ _ _)  , ξ-μ₂ _ p) = notboth _ (W , _ , p)

det : ∀{Φ K}{A A' A'' : Φ ⊢⋆ K}(p : A —→⋆ A')(q : A —→⋆ A'') → A' ≡ A''
det (ξ-⇒₁ p) (ξ-⇒₁ q) = cong (_⇒ _) (det p q)
det (ξ-⇒₁ p) (ξ-⇒₂ w q) = ⊥-elim (notboth _ (w , _ , p))
det (ξ-⇒₂ v p) (ξ-⇒₁ q) = ⊥-elim (notboth _ (v , _ , q))
det (ξ-⇒₂ v p) (ξ-⇒₂ w q) = cong (_ ⇒_) (det p q)
det (ξ-·₁ p) (ξ-·₁ q) = cong (_· _) (det p q)
det (ξ-·₁ p) (ξ-·₂ w q) = ⊥-elim (notboth _ (w , _ , p))
det (ξ-·₂ v p) (ξ-·₁ q) = ⊥-elim (notboth _ (v , _ , q))
det (ξ-·₂ v p) (ξ-·₂ w q) = cong (_ ·_) (det p q)
det (ξ-·₂ v p) (β-ƛ w) = ⊥-elim (notboth _ (w , _ , p))
det (β-ƛ v) (ξ-·₂ w q) = ⊥-elim (notboth _ (v , _ , q))
det (β-ƛ v) (β-ƛ w) = refl
det (ξ-μ₁ p) (ξ-μ₁ q) = cong (λ X → μ X _) (det p q)
det (ξ-μ₁ p) (ξ-μ₂ w q) = ⊥-elim (notboth _ (w , _ , p))
det (ξ-μ₂ v p) (ξ-μ₁ q) = ⊥-elim (notboth _ (v , _ , q))
det (ξ-μ₂ v p) (ξ-μ₂ w q) = cong (μ _) (det p q)
```
