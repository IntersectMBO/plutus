\begin{code}
module Type.Reduction where
\end{code}

## Imports

\begin{code}
open import Data.Product using (Σ)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)

open import Type
open import Type.RenamingSubstitution
\end{code}

## Values

\begin{code}
data Value⋆ :  ∀ {Γ K} → Γ ⊢⋆ K → Set where

  V-Π_ : ∀ {Φ K} {N : Φ ,⋆ K ⊢⋆ *}
      ----------------------------
    → Value⋆ (Π N)

  _V-⇒_ : ∀ {Φ} {S : Φ ⊢⋆ *} {T : Φ ⊢⋆ *}
      -----------------------------------
    → Value⋆ (S ⇒ T)

  V-ƛ_ : ∀ {Φ K J} {N : Φ ,⋆ K ⊢⋆ J}
      ----------------------------
    → Value⋆ (ƛ N)

  V-μ_ : ∀ {Φ K} {N : Φ ,⋆ K ⊢⋆ *}
      ----------------------------
    → Value⋆ (μ N)
\end{code}

## Intrinsically Kind Preserving Type Reduction

\begin{code}
infix 2 _—→⋆_

data _—→⋆_ : ∀ {Γ J} → (Γ ⊢⋆ J) → (Γ ⊢⋆ J) → Set where
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
    → (ƛ N) · W —→⋆ N [ W ]⋆
\end{code}

\begin{code}
data Progress⋆ {K} (M : ∅ ⊢⋆ K) : Set where
  step : ∀ {N : ∅ ⊢⋆ K}
    → M —→⋆ N
      -------------
    → Progress⋆ M
  done :
      Value⋆ M
      ----------
    → Progress⋆ M
\end{code}

\begin{code}
progress⋆ : ∀ {K} → (M : ∅ ⊢⋆ K) → Progress⋆ M
progress⋆ (` ())
progress⋆ (Π M)   = done V-Π_
progress⋆ (M ⇒ N) = done _V-⇒_
progress⋆ (ƛ M)   = done V-ƛ_
progress⋆ (M · N)  with progress⋆ M
...                    | step p = step (ξ-·₁ p)
...                    | done vM with progress⋆ N
...                                | step p = step (ξ-·₂ vM p)
progress⋆ (.(ƛ _) · N) | done V-ƛ_ | done vN = step (β-ƛ vN)
progress⋆ (μ M)   = done V-μ_
\end{code}
