\begin{code}
module TermIndexedBySyntacticType.Term.Reduction where
\end{code}

## Imports

\begin{code}
open import Type
import Type.RenamingSubstitution as ⋆
open import TermIndexedBySyntacticType.Term
open import TermIndexedBySyntacticType.Term.RenamingSubstitution
open import Type.Equality

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Empty
open import Data.Product renaming (_,_ to _,,_)
open import Data.List hiding ([_])
open import Data.List.All
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

  V-wrap1 : ∀{Γ K}
   → {pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
   → {arg : ∥ Γ ∥ ⊢⋆ K}
   → {term : Γ ⊢ pat · (μ1 · pat) · arg}
   → Value (wrap1 pat arg term)

  V-con : ∀{Γ}{s : ∥ Γ ∥ ⊢⋆ #}{tcn : TyCon}
    → (cn : TermCon (con tcn s))
    → Value (con {Γ} cn)
\end{code}

## BUILTIN

\begin{code}
open import Data.Unit
VTel : ∀ Γ Δ → ⋆.Sub ∥ Δ ∥ ∥ Γ ∥ → List (∥ Δ ∥ ⊢⋆ *) → Set
VTel Γ Δ σ [] = ⊤
VTel Γ Δ σ (A ∷ As) = Σ (Γ ⊢ ⋆.subst σ A) λ t → Value t × VTel Γ Δ σ As


{-
BUILTIN : ∀{Γ Γ'}
    → (bn : Builtin)
    → let Δ ,, As ,, C = El bn Γ in
      (σ : ⋆.Sub ∥ Δ ∥ ∥ Γ ∥)
    → (vtel : VTel Γ Δ σ As)
    → (σ' : ⋆.Sub ∥ Γ ∥ ∥ Γ' ∥)
      -----------------------------
    → Γ' ⊢ ⋆.subst σ' (⋆.subst σ C)
BUILTIN addInteger σ (M ,, VM ,, N ,, VN ,, _) σ' = {!!}
BUILTIN substractInteger σ X σ' = {!!}
-}
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

  β-wrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢⋆ K}
    → {term : Γ ⊢ pat · (μ1 · pat) · arg}
    → unwrap1 (wrap1 pat arg term) —→ term

  ξ-unwrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢⋆ K}
    → {M M' : Γ ⊢ μ1 · pat · arg}
    → M —→ M'
    → unwrap1 M —→ unwrap1 M'

  -- this is a temporary hack as currently the type eq relation only has
  -- reflexivity in it.
  ξ-conv₁ : ∀{Γ J}{A : ∥ Γ ∥ ⊢⋆ J}{L : Γ ⊢ A}
    → conv (refl≡β A) L —→ L

  ξ-conv₂ : ∀{Γ J}{A B : ∥ Γ ∥ ⊢⋆ J}{L L' : Γ ⊢ A}{p : A ≡β B}
    → L —→ L'
      --------------------
    → conv p L —→ conv p L'

{-
  β-builtin : ∀{Γ Γ'}
    → (bn : Builtin)
    → let Δ ,, As ,, C = El bn Γ in
      (σ : ⋆.Sub ∥ Δ ∥ ∥ Γ ∥)
    → (tel : Tel Γ Δ σ As)
--    → VTel tel
    → (σ' : ⋆.Sub ∥ Γ ∥ ∥ Γ' ∥)
      -----------------------------
    → builtin bn σ tel σ' —→ {!!} --BUILTIN bn σ tel σ'
-}
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
  unhandled : Progress M 
\end{code}

\begin{code}
progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ M)    = done V-ƛ
progress (L · M)  with progress L
...                   | unhandled = unhandled
...                   | step p  = step (ξ-·₁ p)
progress (.(ƛ _) · M) | done V-ƛ with progress M
progress (.(ƛ _) · M) | done V-ƛ | step p = step (ξ-·₂ V-ƛ p)
progress (.(ƛ _) · M) | done V-ƛ | done VM = step (β-ƛ VM)
progress (.(ƛ _) · M) | done V-ƛ | unhandled = unhandled
progress (Λ M)    = done V-Λ_
progress (M ·⋆ A) with progress M
progress (M ·⋆ A) | step p = step (ξ-·⋆ p)
progress (.(Λ _) ·⋆ A) | done V-Λ_ = step β-Λ
progress (M ·⋆ A) | unhandled = unhandled
progress (wrap1 _ _ t) = done V-wrap1
progress (unwrap1 t) with progress t
progress (unwrap1 t) | step p = step (ξ-unwrap1 p)
progress (unwrap1 .(wrap1 _ _ _)) | done V-wrap1 = step β-wrap1
progress (unwrap1 t) | unhandled = unhandled
progress (conv p t) = unhandled
progress (con cn)   = done (V-con cn)
progress (builtin bn σ X σ') = unhandled
\end{code}
