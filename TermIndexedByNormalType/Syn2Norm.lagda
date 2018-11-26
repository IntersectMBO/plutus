\begin{code}
module TermIndexedByNormalType.Syn2Norm where

open import Type
open import Type.RenamingSubstitution
import TermIndexedBySyntacticType.Term as Syn
import TermIndexedByNormalType.Term as Norm
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.Completeness


open import Relation.Binary.PropositionalEquality renaming (subst to substEq)
open import Function

nfCtx : Syn.Ctx → Norm.Ctx
nfCtx∥ : ∀ Γ → Syn.∥ Γ ∥ ≡ Norm.∥ nfCtx Γ ∥

nfCtx Syn.∅ = Norm.∅
nfCtx (Γ Syn.,⋆ K) = nfCtx Γ Norm.,⋆ K
nfCtx (Γ Syn., A) = nfCtx Γ Norm., substEq (_⊢Nf⋆ _) (nfCtx∥ Γ) (nf A)

nfCtx∥ Syn.∅ = refl
nfCtx∥ (Γ Syn.,⋆ K) = cong (_,⋆ K) (nfCtx∥ Γ)
nfCtx∥ (Γ Syn., A)  = nfCtx∥ Γ

lem∥ : ∀{Γ Γ'} → Γ ≡ Γ' → Norm.∥ Γ ∥ ≡ Norm.∥ Γ ∥
lem∥ refl = refl

lemX : ∀{Γ Γ' K J}{A : Γ ⊢Nf⋆ K}{A' : Γ ,⋆ J ⊢Nf⋆ K}
 → (p : Γ ≡ Γ')
 → (q : Γ ,⋆ J ≡ Γ' ,⋆ J)
 → renameNf S A ≡ A'
 → renameNf S (substEq (_⊢Nf⋆ K) p A) ≡ substEq (_⊢Nf⋆ K) q A'
lemX refl refl p = p

subst∋ : ∀ {Γ Γ' K}{A : Norm.∥ Γ ∥ ⊢Nf⋆ K}{A' : Norm.∥ Γ' ∥ ⊢Nf⋆ K}
 → (p : Γ ≡ Γ')
 → substEq (_⊢Nf⋆ K) (cong Norm.∥_∥ p) A ≡ A' →
 (Γ Norm.∋ A) → Γ' Norm.∋ A'
subst∋ refl refl α = α

nfTyVar : ∀{Γ K}
  → {A : Syn.∥ Γ ∥ ⊢⋆ K}
  → Γ Syn.∋ A
  → nfCtx Γ Norm.∋ substEq (_⊢Nf⋆ K) (nfCtx∥ Γ) (nf A)
nfTyVar {Γ Syn., A}{J} Syn.Z = Norm.Z
nfTyVar (Syn.S α) =  Norm.S (nfTyVar α)
nfTyVar (Syn.T {Γ}{K}{J}{A} α) = subst∋ refl (lemX (nfCtx∥ Γ) (cong (_,⋆ J) (nfCtx∥ Γ)) (trans (rename-reify (idext idCR A) S) (reifyCR (transCR (transCR (renameVal-eval A idCR S) (idext (renameVal-reflect S ∘ `) A)) (symCR (rename-eval A idCR S)))))) (Norm.T (nfTyVar α))

{-
nfType : ∀{Γ K}
  → {A : Syn.∥ Γ ∥ ⊢⋆ K}
  → Γ Syn.⊢ A
  → nfCtx Γ Norm.⊢ substEq (_⊢Nf⋆ K) (nfCtx∥ Γ) (nf A)
nfType (Syn.` x) = Norm.` (nfTyVar x)
nfType (Syn.ƛ x) = {!nfType x!}
nfType (x Syn.· x₁) = {!!}
nfType (Syn.Λ x) = {!!}
nfType (x Syn.·⋆ A) = {!!}
nfType (Syn.wrap1 pat arg x) = {!!}
nfType (Syn.unwrap1 x) = {!!}
nfType (Syn.conv x x₁) = {!!}
nfType (Syn.con x) = {!!}
nfType (Syn.builtin bn σ x) = {!!}
nfType (Syn.error A) = {!!}
-}
\end{code}
