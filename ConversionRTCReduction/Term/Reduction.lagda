\begin{code}
module Term.Reduction where
\end{code}

## Imports

\begin{code}
open import Type
import Type.RenamingSubstitution as ⋆
open import Term
open import Term.RenamingSubstitution
open import Type.Reduction
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

data _—→_ : ∀ {J Γ} {A A' : ∥ Γ ∥ ⊢⋆ J} → (Γ ⊢ A) → (Γ ⊢ A') → Set where

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

  ξ-conv₁ : ∀{Γ J}{A B C : ∥ Γ ∥ ⊢⋆ J}{L : Γ ⊢ A}
    → (p : B —↠⋆ A)
    → (q : C —→⋆ B)
    → conv (trans—↠⋆ C q p) L —→ conv p L

  ξ-conv₂ : ∀{Γ J}{A : ∥ Γ ∥ ⊢⋆ J}{L : Γ ⊢ A}
    → conv refl—↠⋆ L —→ L


  ξ-conv₃ : ∀{Γ J}{A B : ∥ Γ ∥ ⊢⋆ J}{L L' : Γ ⊢ A}{p : B —↠⋆ A}
    → L —→ L'
    → conv p L —→ conv p L'
\end{code}


Transitive closure of reduction
\begin{code}
data _—↠_ {J Γ}{A : ∥ Γ ∥ ⊢⋆ J} (L : Γ ⊢ A) : (Γ ⊢ A) → Set where
  done : L —↠ L
  continue : ∀ {M N} → L —→ M → M —↠ N → L —↠ N  
\end{code}

\begin{code}
data Progress {A : ∅ ⊢⋆ *} (M : ∅ ⊢ A) : Set where
  step : ∀ {A'}{N : ∅ ⊢ A'}
    → M —→ N
      -------------
    → Progress M
  done :
      Value M
      ----------
    → Progress M
  unhandled-conversion : Progress M 
\end{code}

\begin{code}
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum
{-
progress : ∀ {A : ∅ ⊢⋆ *} → (M : ∅ ⊢ A) →
  Value M ⊎ Σ (∅ ⊢⋆ *) λ A' → Σ (∅ ⊢ A') (λ M' → M —→ M')
progress (` ())
progress (ƛ M)      = inj₁ V-ƛ
progress (M · N)    with progress M
progress (M · N) | inj₂ (A ,, M' ,, p) = inj₂ ({!!} ,, {!!} ,, {!ξ-·₁ p!})
progress (M · N) | inj₁ VM with progress N
progress (.(ƛ _) · N) | inj₁ V-ƛ | inj₁ VN = inj₂ (_ ,, _ ,, β-ƛ VN)
progress (M · N) | inj₁ VM | inj₂ p = {!!}

progress (Λ M)      = inj₁ V-Λ_
progress (M ·⋆ A)   = {!!}
progress (wrap A M) = inj₁ V-wrap
progress (unwrap M) = {!!}
progress (conv refl—↠⋆ M)          = inj₂ (_ ,, M ,, ξ-conv₂)
progress (conv (trans—↠⋆ L p q) M) = inj₂ (_ ,, conv q M ,, ξ-conv₁ q p)
-}
{-
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ M)    = done V-ƛ
progress (L · M)  with progress L
...                   | unhandled-conversion = unhandled-conversion
...                   | step p  = step (ξ-·₁ p)
...                   | done vL with progress M
...                              | unhandled-conversion = unhandled-conversion
...                              | step p  = step (ξ-·₂ vL p)
progress (.(ƛ _) · M) | done V-ƛ | done vM = step (β-ƛ vM)
progress (Λ M)    = done V-Λ_
progress (M ·⋆ A) with progress M
...                    | unhandled-conversion = unhandled-conversion
...                    | step p  = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = step β-Λ
progress (wrap A M) = done V-wrap
progress (unwrap M) with progress M
...                           | unhandled-conversion = unhandled-conversion
...                           | step p = step (ξ-unwrap p)
progress (unwrap .(wrap _ _)) | done V-wrap = step β-wrap
progress (conv p t) = unhandled-conversion
-}
\end{code}
