\begin{code}
module TermIndexedByNormalType.Term.Reduction where
\end{code}

## Imports

\begin{code}
open import Type
open import TermIndexedByNormalType.Term
open import TermIndexedByNormalType.Term.RenamingSubstitution
open import Type.BetaNBE
open import Type.BetaNBE.Stability
open import Type.BetaNBE.RenamingSubstitution
open import Type.BetaNormal
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢Nf⋆_ con size⋆

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Data.Sum
open import Function

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

  V-wrap1 : ∀{Γ K}
   → {pat : ∥ Γ ∥ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {arg : ∥ Γ ∥ ⊢Nf⋆ K}
   → {term : Γ ⊢  nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
   → Value (wrap1 pat arg term)

  V-con : ∀{Γ}{n}{tcn : TyCon}
    → (cn : TermCon (con tcn (size⋆ n)))
    → Value (con {Γ} cn)

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

  β-wrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢Nf⋆ K}
    → {term : Γ ⊢  nf (embNf pat · (μ1 · embNf pat) · embNf arg)}
    → unwrap1 (wrap1 pat arg term) —→ term

  ξ-unwrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢Nf⋆ K}
    → {M M' : Γ ⊢ ne (μ1 · pat · arg)}
    → M —→ M'
    → unwrap1 M —→ unwrap1 M'

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
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ M) = done V-ƛ
progress (M · N) with progress M
progress (M · N) | step p = step (ξ-·₁ p)
progress (.(ƛ _) · N) | done V-ƛ with progress N
progress (.(ƛ _) · N) | done V-ƛ | step p = step (ξ-·₂ V-ƛ p)
progress (.(ƛ _) · N) | done V-ƛ | done VN = step (β-ƛ VN)
progress (Λ M) = done V-Λ_
progress (M ·⋆ A) with progress M
progress (M ·⋆ A) | step p = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = step β-Λ
progress (wrap1 pat arg term) = done V-wrap1
progress (unwrap1 term)       with progress term
progress (unwrap1 term) | step p = step (ξ-unwrap1 p)
progress (unwrap1 .(wrap1 _ _ _)) | done V-wrap1 = step β-wrap1
progress (con (integer s i x))    = done (V-con _)
progress (con (bytestring s b x)) = done (V-con _)
progress (con (TermCon.size s))   = done (V-con _)
