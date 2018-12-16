\begin{code}
module TermIndexedByNormalType.Norm2Syn where

open import Type
open import Type.RenamingSubstitution
import TermIndexedBySyntacticType.Term as Syn
import TermIndexedByNormalType.Term as Norm
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.Completeness
open import Relation.Binary.PropositionalEquality renaming (subst to substEq)
open import TermIndexedByNormalType.Syn2Norm 
\end{code}

\begin{code}
embCtx : Norm.Ctx → Syn.Ctx
embCtx∥ : ∀ Γ → Norm.∥ Γ ∥ ≡ Syn.∥ embCtx Γ ∥

embCtx Norm.∅       = Syn.∅
embCtx (Γ Norm.,⋆ K) = embCtx Γ Syn.,⋆ K
embCtx (Γ Norm., A)  = embCtx Γ Syn., substEq (_⊢⋆ _) (embCtx∥ Γ) (embNf A)

embCtx∥ Norm.∅       = refl
embCtx∥ (Γ Norm.,⋆ K) = cong (_,⋆ K) (embCtx∥ Γ)
embCtx∥ (Γ Norm., A)  = embCtx∥ Γ
\end{code}


\begin{code}
lemT' : ∀{Γ Γ' J K}(A :  Γ ⊢Nf⋆ K)
 → (p : Γ ≡ Γ')
 → (q : Γ ,⋆ J ≡ Γ' ,⋆ J)
  → weaken (substEq (_⊢⋆ K) p (embNf A))
    ≡
    substEq (_⊢⋆ K) q (embNf (renameNf S A))
lemT' A refl refl = sym (rename-embNf S A)
\end{code}

\begin{code}
subst∋' : ∀ {Γ Γ' K}{A : Syn.∥ Γ ∥ ⊢⋆ K}{A' : Syn.∥ Γ' ∥ ⊢⋆ K}
 → (p : Γ ≡ Γ')
 → substEq (_⊢⋆ K) (cong Syn.∥_∥ p) A ≡ A' →
 (Γ Syn.∋ A) → Γ' Syn.∋ A'
subst∋' refl refl α = α
\end{code}

\begin{code}
embTyVar : ∀{Γ K}{A : Norm.∥ Γ ∥ ⊢Nf⋆ K}
  → Γ Norm.∋ A
  → embCtx Γ Syn.∋ substEq (_⊢⋆ K) (embCtx∥ Γ) (embNf A)
embTyVar Norm.Z     = Syn.Z
embTyVar (Norm.S α) = Syn.S (embTyVar α)
embTyVar {Γ Norm.,⋆ K} (Norm.T {A = A} α) = subst∋'
  refl
  (lemT' A (embCtx∥ Γ) (embCtx∥ (Γ Norm.,⋆ K)))
  (Syn.T (embTyVar α))
\end{code}

\begin{code}
subst⊢' : ∀ {Γ Γ' K}{A : Syn.∥ Γ ∥ ⊢⋆ K}{A' : Syn.∥ Γ' ∥ ⊢⋆ K}
 → (p : Γ ≡ Γ')
 → substEq (_⊢⋆ K) (cong Syn.∥_∥ p) A ≡ A' →
 (Γ Syn.⊢ A) → Γ' Syn.⊢ A'
subst⊢' refl refl α = α
\end{code}


\begin{code}
lemƛ' : ∀{Γ Γ'}(A B : Γ ⊢Nf⋆ *) →
      (p : Γ ≡ Γ') → 
      substEq (_⊢⋆ *) p (embNf A ⇒ embNf B)
      ≡
      substEq (_⊢⋆ *) p (embNf A) ⇒ substEq (_⊢⋆ *) p (embNf B)
lemƛ' A B refl = refl
\end{code}

\begin{code}
embTy : ∀{Γ K}{A : Norm.∥ Γ ∥ ⊢Nf⋆ K}
  → Γ Norm.⊢ A
  → embCtx Γ Syn.⊢ substEq (_⊢⋆ K) (embCtx∥ Γ) (embNf A)
embTy (Norm.` α) = Syn.` (embTyVar α)
embTy {Γ} (Norm.ƛ {A = A}{B} t) =
  subst⊢' refl (sym (lemƛ' A B (embCtx∥ Γ)) ) (Syn.ƛ (embTy t))
embTy (t Norm.· u) = {!embTy t Syn.· embTy u!}
embTy (Norm.Λ t) = {!Syn.Λ (embTy t)!}
embTy (t Norm.·⋆ A) = {!!}
embTy (Norm.wrap1 pat arg t) = {!!}
embTy (Norm.unwrap1 t) = {!!}
embTy (Norm.con t) = {!!}
embTy (Norm.builtin bn σ tel) = {!!}
embTy {Γ} (Norm.error A) = Syn.error (substEq (_⊢⋆ _) (embCtx∥ Γ) (embNf A) )
\end{code}
