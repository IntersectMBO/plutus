\begin{code}
module TermIndexedByNormalType.Term.Reduction where
\end{code}

## Imports

\begin{code}
open import Type
open import TermIndexedByNormalType.Term
open import TermIndexedByNormalType.Term.RenamingSubstitution
open import Type.BetaNBE
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal
\end{code}

## Values

\begin{code}
data Value :  ∀ {J Γ} {A : ∥ Γ ∥ ⊢Nf⋆ J} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-Λ_ : ∀ {Γ K} {B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}
    → {N : Γ ,⋆ K ⊢ B}
      ----------------
    → Value (Λ N)

  V-wrap : ∀{Γ}
    → {A : ∥ Γ ∥ ,⋆ * ⊢Nf⋆ *}
    → {M : Γ ⊢ (A [ μ A ]Nf)}
      ----------------
    → Value (wrap {B = A} M)

\end{code}

## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {J Γ} {A : ∥ Γ ∥ ⊢Nf⋆ J} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′
    
  ξ-·⋆ : ∀ {Γ K}{B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}{L L′ : Γ ⊢ Π B}{A}
    → L —→ L′
      -----------------
    → L ·⋆ A —→ L′ ·⋆ A

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      -------------------
    → (ƛ N) · W —→ N [ W ]

  β-Λ : ∀ {Γ K}{B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}{N : Γ ,⋆ K ⊢ B}{W}
      -------------------
    → (Λ N) ·⋆ W —→ N [ W ]⋆

  ξ-unwrap : ∀{Γ}
    → {A : ∥ Γ ∥ ,⋆ * ⊢Nf⋆ *}
    → {M M' : Γ ⊢ μ A}
    → M —→ M'
    → unwrap M —→ unwrap M'

  β-wrap : ∀{Γ}
    → {S : ∥ Γ ∥ ,⋆ * ⊢Nf⋆ *}
    → {M : Γ ⊢ S [ μ S ]Nf}    
    → unwrap (wrap {B = S} M) —→ M
\end{code}

\begin{code}
data _—↠_ {J Γ} : {A : ∥ Γ ∥ ⊢Nf⋆ J}{A' : ∥ Γ ∥ ⊢Nf⋆ J} → (Γ ⊢ A) → (Γ ⊢ A') → Set where

  refl—↠ : ∀{A}{M : Γ ⊢ A}
      --------
    → M —↠ M

  trans—↠ : {A : ∥ Γ ∥ ⊢Nf⋆ J}
    {M  M' M'' : Γ ⊢ A}
    → M —→ M'
    → M' —↠ M''
      ---------
    → M —↠ M''
\end{code}

\begin{code}
data Progress {A : ∅ ⊢Nf⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀{N}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M
\end{code}

\begin{code}
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ M) = done V-ƛ
progress (M · N) with progress M
progress (M · N) | step p = step (ξ-·₁ p)
progress (M · N) | done VM with progress N
progress (M · N) | done VM | step q = step (ξ-·₂ VM q)
progress (.(ƛ _) · N) | done V-ƛ | done VN = step (β-ƛ VN)

progress (Λ M) = done V-Λ_
progress (M ·⋆ A) with progress M
progress (M ·⋆ A) | step p  = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = step β-Λ
progress (wrap M) = done V-wrap
progress (unwrap M) with progress M
progress (unwrap M) | step x = step (ξ-unwrap x)
progress (unwrap .(wrap _)) | done V-wrap = step β-wrap
