\begin{code}
module Scoped.Extrication.RenamingSubstitution where
\end{code}

erasure commutes with renaming/substitution

\begin{code}
open import Type
open import Type.BetaNormal
open import Data.Nat
open import Data.Fin
open import Function hiding (_∋_)
open import Relation.Binary.PropositionalEquality as Eq
open import Algorithmic as A
open import Type.RenamingSubstitution as T
open import Scoped
open import Scoped.Extrication
open import Algorithmic.RenamingSubstitution as AS
open import Scoped.RenamingSubstitution as SS
open import Builtin

-- type renamings

extricateRenNf⋆ : ∀{Γ Δ}(ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J) 
  → Ren⋆ (len⋆ Γ) (len⋆ Δ)
extricateRenNf⋆ {Γ ,⋆ K} ρ⋆ zero = extricateVar⋆ (ρ⋆ Z)
extricateRenNf⋆ {Γ ,⋆ K} ρ⋆ (suc α) = extricateRenNf⋆ (ρ⋆ ∘ S) α

ren-extricateVar⋆ : ∀{Γ Δ J}
  → (ρ⋆ : ∀ {J} → Γ ∋⋆ J → Δ ∋⋆ J)
  → (α : Γ ∋⋆ J)
  → extricateRenNf⋆ ρ⋆ (extricateVar⋆ α) ≡ extricateVar⋆ (ρ⋆ α)
ren-extricateVar⋆ ρ⋆ Z     = refl
ren-extricateVar⋆ ρ⋆ (S α) = ren-extricateVar⋆ (ρ⋆ ∘ S) α

-- term level renamings

extricateRen : ∀{Φ Ψ Γ Δ}(ρ⋆ : ∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J) →
  (ρ : ∀{J}{A : Φ ⊢Nf⋆ J} → Γ ∋ A → Δ ∋ renameNf ρ⋆ A)
  → SS.Ren (len Γ) (len Δ)
extricateRen {Γ = Γ ,⋆ J} {Δ} ρ⋆ ρ (T x) = extricateRen
  (ρ⋆ ∘ S)
  (λ {_}{A} x → Eq.subst (Δ ∋_) (sym (renameNf-comp A)) (ρ (T x)))
  x
extricateRen {Γ = Γ , A}  {Δ} ρ⋆ ρ Z     = extricateVar (ρ Z)
extricateRen {Γ = Γ , A}  {Δ} ρ⋆ ρ (S x) = extricateRen ρ⋆ (ρ ∘ S) x


-- these are the two properties of extrication/ren/sub needed to define
-- extricate—→

postulate
  lem[] : ∀{Φ Γ}{A B : Φ ⊢Nf⋆ *}(N : Γ , A ⊢ B)(W : Γ ⊢ A)
    → extricate N SS.[ extricate W ] ≡ extricate (N AS.[ W ])

  lem[]⋆ : ∀{Φ Γ K}{B : Φ ,⋆ K ⊢Nf⋆ *}(N : Γ ,⋆ K ⊢ B)(A : Φ ⊢Nf⋆ K)
    → extricate N SS.[ extricateNf⋆ A ]⋆ ≡ extricate (N AS.[ A ]⋆)
\end{code}
