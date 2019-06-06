\begin{code}
module Algorithmic.Erasure.Reduction where
\end{code}

\begin{code}
open import Type
open import Type.BetaNormal
open import Algorithmic
import Algorithmic.Reduction as A
open import Algorithmic.Erasure
import Untyped.Reduction as U

open import Data.Sum
open import Relation.Binary.PropositionalEquality
\end{code}

\begin{code}
erase—→ : ∀{Φ}{A : Φ ⊢Nf⋆ *}{Γ : Ctx Φ}{t t' : Γ ⊢ A}
  → t A.—→ t' → erase t U.—→ erase t' ⊎ erase t ≡ erase t'
erase—→ (A.ξ-Λ p)                                       = erase—→ p
erase—→ (A.ξ-·₁ p)                                      = {!!}
erase—→ (A.ξ-·₂ p q)                                    = {!!}
erase—→ (A.ξ-·⋆ p)                                      = {!!}
erase—→ A.β-ƛ                                           = {!!}
erase—→ A.β-Λ                                           = {!!}
erase—→ A.β-wrap1                                       = {!!}
erase—→ (A.ξ-unwrap1 p)                                 = erase—→ p
erase—→ (A.ξ-wrap p)                                    = erase—→ p
erase—→ (A.β-builtin bn σ tel vtel)                     = {!!}
erase—→ (A.ξ-builtin bn σ tel Bs Ds telB telD vtel x p) = {!!}
\end{code}
