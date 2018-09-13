\begin{code}
module Type.Reduction where
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution

open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)
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

\begin{code}
renameValue⋆ : ∀ {Φ Ψ}
  → (ρ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → ∀ {J}{A : Φ ⊢⋆ J} → Value⋆ A → Value⋆ (rename ρ A)
renameValue⋆ ρ V-Π_  = V-Π_
renameValue⋆ ρ _V-⇒_ = _V-⇒_
renameValue⋆ ρ V-ƛ_  = V-ƛ_
renameValue⋆ ρ V-μ_  = V-μ_
\end{code}

\begin{code}
substValue⋆ : ∀ {Φ Ψ}
  → (σ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
    ----------------------------
  → ∀ {J}{A : Φ ⊢⋆ J} → Value⋆ A → Value⋆ (subst σ A)
substValue⋆ σ V-Π_  = V-Π_
substValue⋆ σ _V-⇒_ = _V-⇒_
substValue⋆ σ V-ƛ_   = V-ƛ_
substValue⋆ σ V-μ_   = V-μ_
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
    → (ƛ N) · W —→⋆ N [ W ]
\end{code}

\begin{code}
rename—→⋆ : ∀{Φ Ψ J}{A B : Φ ⊢⋆ J}
  → (ρ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → A —→⋆ B
    ----------------------------
  → rename ρ A —→⋆ rename ρ B
rename—→⋆ ρ (ξ-·₁ p)               = ξ-·₁ (rename—→⋆ ρ p)
rename—→⋆ ρ (ξ-·₂ V p)             = ξ-·₂ (renameValue⋆ ρ V) (rename—→⋆ ρ p)
rename—→⋆ ρ (β-ƛ {N = M}{W = N} V) =
  substEq (λ X → rename ρ ((ƛ M) · N) —→⋆ X)
          (trans (sym (subst-rename (ext ρ) (subst-cons `_ (rename ρ N)) M))
                 (trans (subst-cong _ _ (rename-subst-cons ρ N) M)
                        (rename-subst (subst-cons `_ N) ρ M)))
          (β-ƛ {N = rename (ext ρ) M}{W = rename ρ N} (renameValue⋆ ρ V)) 
\end{code}

\begin{code}
subst—→⋆ : ∀{Φ Ψ J}{A B : Φ ⊢⋆ J}
  → (σ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  → A —→⋆ B
    ----------------------------
  → subst σ A —→⋆ subst σ B
subst—→⋆ σ (ξ-·₁ p) = ξ-·₁ (subst—→⋆ σ p)
subst—→⋆ σ (ξ-·₂ V p) = ξ-·₂ (substValue⋆ σ V) (subst—→⋆ σ p)
subst—→⋆ σ (β-ƛ {N = M}{W = N} V) =
  substEq (λ X → subst σ ((ƛ M) · N) —→⋆ X)
          (trans (sym (subst-comp (exts σ) (subst-cons `_ (subst σ N)) M))
                 (trans (subst-cong _ _ (subst-subst-cons σ N) M)
                        (subst-comp (subst-cons `_ N) σ M)))
          (β-ƛ {N = subst (exts σ) M}{W = subst σ N} (substValue⋆ σ V))
\end{code}

\begin{code}
data _—↠⋆_ {J Γ} :  (Γ ⊢⋆ J) → (Γ ⊢⋆ J) → Set where

  refl—↠⋆ : ∀{M}
      --------
    → M —↠⋆ M

  trans—↠⋆ : (L : Γ ⊢⋆ J) {M N : Γ ⊢⋆ J}
    → L —→⋆ M
    → M —↠⋆ N
      ---------
    → L —↠⋆ N
\end{code}

\begin{code}
rename—↠⋆ : ∀{Φ Ψ J}{A B : Φ ⊢⋆ J}
  → (ρ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
  → A —↠⋆ B
    ----------------------------
  → rename ρ A —↠⋆ rename ρ B
rename—↠⋆ ρ refl—↠⋆          = refl—↠⋆
rename—↠⋆ ρ (trans—↠⋆ L p q) =
  trans—↠⋆ (rename ρ L) (rename—→⋆ ρ p) (rename—↠⋆ ρ q)
\end{code}

\begin{code}
subst—↠⋆ : ∀{Φ Ψ J}{A B : Φ ⊢⋆ J}
  → (σ : ∀ {J} → Φ ∋⋆ J → Ψ ⊢⋆ J)
  → A —↠⋆ B
    ----------------------------
  → subst σ A —↠⋆ subst σ B
subst—↠⋆ σ refl—↠⋆          = refl—↠⋆
subst—↠⋆ σ (trans—↠⋆ L p q) =
  trans—↠⋆ (subst σ L) (subst—→⋆ σ p) (subst—↠⋆ σ q)
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
open import Data.Product
open import Data.Sum

progress⋆ : ∀ {K} → (M : ∅ ⊢⋆ K) → Value⋆ M ⊎ Σ (∅ ⊢⋆ K) λ M' → M —→⋆ M'  
progress⋆ (` ())
progress⋆ (Π M)   = inj₁ V-Π_
progress⋆ (M ⇒ N) = inj₁ _V-⇒_
progress⋆ (ƛ M)   = inj₁ V-ƛ_
progress⋆ (M · N) with progress⋆ M
progress⋆ (M · N) | inj₁ vM with progress⋆ N
progress⋆ (.(ƛ _) · N) | inj₁ (V-ƛ_ {N = M}) | inj₁ vN =
  inj₂ ((M [ N ]) , (β-ƛ vN))
progress⋆ (M · N) | inj₁ vM | inj₂ (N' , p) = inj₂ (M · N'  , ξ-·₂ vM p)
progress⋆ (M · N) | inj₂ (M' , p)  = inj₂ (M' · N , (ξ-·₁ p))
progress⋆ (μ M)   = inj₁ V-μ_

{-
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
-}
\end{code}
