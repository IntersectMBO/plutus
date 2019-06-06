\begin{code}
module Algorithmic.Erasure.RenamingSubstitution where
\end{code}

\begin{code}
open import Type
open import Type.BetaNormal
open import Algorithmic
open import Algorithmic.RenamingSubstitution
open import Algorithmic.Erasure

open import Data.Fin
import Data.Product as P
\end{code}

\begin{code}
backVar : ∀{Φ}{Γ : Ctx Φ} → Fin (len Γ) → P.Σ (Φ ⊢Nf⋆ *) λ A → Γ ∋ A
backVar {Γ = Γ ,⋆ J} x = let
  A P., x = backVar {Γ = Γ} x
  in
  weakenNf A P., T x
backVar {Γ = Γ , A} zero = {!A!} P., {!!}
backVar {Γ = Γ , A} (suc x) = {!!}
\end{code}
