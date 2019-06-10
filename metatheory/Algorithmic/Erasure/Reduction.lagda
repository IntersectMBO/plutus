\begin{code}
module Algorithmic.Erasure.Reduction where
\end{code}

\begin{code}
open import Type
open import Type.BetaNormal
open import Algorithmic
import Algorithmic.Reduction as A
import Algorithmic.RenamingSubstitution as A
open import Algorithmic.Erasure
import Untyped.Reduction as U
import Untyped.RenamingSubstitution as U
open import Untyped

open import Data.Sum
open import Relation.Binary.PropositionalEquality
\end{code}

\begin{code}
erase—→ : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : Ctx Φ}{t t' : Γ ⊢ A}
  → t A.—→ t' → erase t U.—→ erase t' ⊎ erase t ≡ erase t'
erase—→ (A.ξ-Λ p)                                       = erase—→ p
erase—→ (A.ξ-·₁ {M = M} p)                              = map
  U.ξ-·₁
  (cong (_· erase M))
  (erase—→ p)
erase—→ (A.ξ-·₂ {V = V} p q)                                    = map
  (U.ξ-·₂ {!!})
  ((cong (erase V ·_)))
  (erase—→ q)
erase—→ (A.ξ-·⋆ p)                                      = erase—→ p
erase—→ (A.β-ƛ {x = x}{N = N}{W = W})                   =
  inj₁ (subst ((ƛ x (erase N) · erase W) U.—→_) {!!} U.β-ƛ)
erase—→ A.β-Λ                                           =
  inj₂ {!!}
erase—→ A.β-wrap1                                       = inj₂ refl
erase—→ (A.ξ-unwrap1 p)                                 = erase—→ p
erase—→ (A.ξ-wrap p)                                    = erase—→ p
erase—→ (A.β-builtin bn σ tel vtel)                     = {!U.β-builtin!}
erase—→ (A.ξ-builtin bn σ tel Bs Ds telB telD vtel x p) = {!U.ξ-builtin!}
\end{code}
