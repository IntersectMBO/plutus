\begin{code}
module Algorithmic.Erasure.Reduction where
\end{code}

\begin{code}
open import Type
open import Type.BetaNormal
open import Algorithmic as A
import Algorithmic.Reduction as A
import Algorithmic.RenamingSubstitution as A
open import Algorithmic.Erasure
open import Algorithmic.Erasure.RenamingSubstitution
import Untyped.Reduction as U
import Untyped.RenamingSubstitution as U
open import Untyped

open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Data.List hiding (map)
open import Data.Product hiding (map) renaming (_,_ to _,,_)
open import Data.Unit
\end{code}

\begin{code}
eraseVal : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : Ctx Φ}{t : Γ ⊢ A}
  → A.Value t → U.Value (erase t)
eraseVal (A.V-ƛ {N = t})      = U.V-ƛ (erase t)
eraseVal (A.V-Λ v)            = eraseVal v
eraseVal (A.V-wrap v)         = eraseVal v
eraseVal (A.V-con {Γ = Γ} cn) = U.V-con (eraseTC {Γ = Γ} cn)

eraseVTel : ∀ {Φ} Γ Δ
  → (σ : ∀ {K} → Δ ∋⋆ K → Φ ⊢Nf⋆ K)
  → (As : List (Δ ⊢Nf⋆ *))
  → (tel : A.Tel Γ Δ σ As)
  → (vtel : A.VTel Γ Δ σ As tel)
  → U.VTel (len Γ) (eraseTel tel)
eraseVTel Γ Δ σ []       tel        vtel        = _ 
eraseVTel Γ Δ σ (A ∷ As) (t ,, tel) (v ,, vtel) =
  eraseVal v ,, eraseVTel Γ Δ σ As tel vtel 
\end{code}

\begin{code}
erase—→ : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : Ctx Φ}{t t' : Γ ⊢ A}
  → t A.—→ t' → erase t U.—→ erase t' ⊎ erase t ≡ erase t'
erase—→ (A.ξ-Λ p)                                       = erase—→ p
erase—→ (A.ξ-·₁ {M = M} p)                              = map
  U.ξ-·₁
  (cong (_· erase M))
  (erase—→ p)
erase—→ (A.ξ-·₂ {V = V} p q)                            = map
  (U.ξ-·₂ (eraseVal p))
  ((cong (erase V ·_)))
  (erase—→ q)
erase—→ (A.ξ-·⋆ p)                                      = erase—→ p
erase—→ (A.β-ƛ {x = x}{N = N}{W = W})                   =
  inj₁ (subst ((ƛ x (erase N) · erase W) U.—→_) (lem[] N W) U.β-ƛ)
erase—→ (A.β-Λ {N = N}{A = A})                          =
  inj₂ (lem[]⋆ N A)
erase—→ A.β-wrap1                                       = inj₂ refl
erase—→ (A.ξ-unwrap1 p)                                 = erase—→ p
erase—→ (A.ξ-wrap p)                                    = erase—→ p
erase—→ (A.β-builtin bn σ tel vtel)                     = inj₁ ?
erase—→ (A.ξ-builtin bn σ tel Bs Ds telB telD vtel p q) with erase—→ p
erase—→ (A.ξ-builtin bn σ tel Bs Ds telB telD vtel p q) | inj₁ x
  = inj₁ {!U.ξ-builtin!}
erase—→ (A.ξ-builtin bn σ tel Bs Ds telB telD vtel p q) | inj₂ y
  = {!refl!}
\end{code}
