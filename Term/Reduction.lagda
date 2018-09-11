\begin{code}
module Term.Reduction where
\end{code}

## Imports

\begin{code}
open import Type
import Type.RenamingSubstitution as ⋆
open import Term
open import Term.RenamingSubstitution
\end{code}

## Values

\begin{code}
data Value :  ∀ {J Γ} {A : ∥ Γ ∥ ⊢⋆ J} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-Λ_ : ∀ {Γ K} {B : ∥ Γ ∥ ,⋆ K ⊢⋆ *}
    → {N : Γ ,⋆ K ⊢ B}
      ----------------
    → Value (Λ N)

  V-wrap : ∀{Γ}
    → {S : ∥ Γ ∥ ,⋆ * ⊢⋆ *}
    → {M : Γ ⊢ S ⋆.[ μ S ]}
      ----------------
    → Value (wrap S M)
\end{code}

## Intrinsically Type Preserving Reduction

\begin{code}
infix 2 _—→_

data _—→_ : ∀ {J Γ} {A : ∥ Γ ∥ ⊢⋆ J} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      -----------------
    → L · M —→ L′ · M

  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      --------------
    → V · M —→ V · M′

  ξ-·⋆ : ∀ {Γ B}{L L′ : Γ ⊢ Π B}{A}
    → L —→ L′
      -----------------
    → L ·⋆ A —→ L′ ·⋆ A
    
  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      -------------------
    → (ƛ N) · W —→ N [ W ]

  β-Λ : ∀ {Γ}{B : ∥ Γ ∥ ,⋆ * ⊢⋆ *}{N : Γ ,⋆ * ⊢ B}{W}
      -------------------
    → (Λ N) ·⋆ W —→ N [ W ]⋆

  ξ-unwrap : ∀{Γ}
    → {S : ∥ Γ ∥ ,⋆ * ⊢⋆ *}
    → {M M' : Γ ⊢ μ S}
    → M —→ M'
    → unwrap M —→ unwrap M'

  β-wrap : ∀{Γ}
    → {S : ∥ Γ ∥ ,⋆ * ⊢⋆ *}
    → {M : Γ ⊢ S ⋆.[ μ S ]}    
    → unwrap (wrap S M) —→ M

  -- this is a temporary hack as currently the type eq relation only has
  -- reflexivity in it.
  ξ-conv₁ : ∀{Γ J}{A : ∥ Γ ∥ ⊢⋆ J}{L : Γ ⊢ A}
    → conv (refl A) L —→ L

  ξ-conv₂ : ∀{Γ J}{A B : ∥ Γ ∥ ⊢⋆ J}{L L' : Γ ⊢ A}{p : A ≡β B}
    → L —→ L'
    → conv p L —→ conv p L'
\end{code}


\begin{code}
data Progress {A : ∅ ⊢⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀ {N}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M
\end{code}

\begin{code}
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ M)    = done V-ƛ
progress (L · M)  with progress L
...                   | step p  = step (ξ-·₁ p)
...                   | done vL with progress M
...                              | step p  = step (ξ-·₂ vL p)
progress (.(ƛ _) · M) | done V-ƛ | done vM = step (β-ƛ vM)
progress (Λ M)    = done V-Λ_
progress (M ·⋆ A) with progress M
progress (M ·⋆ A)      | step p  = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = step β-Λ
progress (wrap A M) = done V-wrap
progress (unwrap M) with progress M
progress (unwrap M) | step p = step (ξ-unwrap p)
progress (unwrap .(wrap _ _)) | done V-wrap = step β-wrap
progress (conv (refl A) t) = step ξ-conv₁
\end{code}
