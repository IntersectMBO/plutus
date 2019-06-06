\begin{code}
module Algorithmic.Erasure.RenamingSubstitution where
\end{code}

\begin{code}
open import Type
import Type.RenamingSubstitution as ⋆
open import Type.BetaNormal
open import Type.BetaNBE.RenamingSubstitution
open import Algorithmic
import Algorithmic.RenamingSubstitution as A
open import Algorithmic.Erasure
import Untyped.RenamingSubstitution as U

open import Data.Fin
import Data.Product as P
\end{code}

\begin{code}
backVar : ∀{Φ}{Γ : Ctx Φ} → Fin (len Γ) → P.Σ (Φ ⊢Nf⋆ *) λ A → Γ ∋ A
backVar {Γ = Γ ,⋆ J} x = let
  A P., x = backVar {Γ = Γ} x
  in
  weakenNf A P., T x
backVar {Γ = Γ , A} zero = A P., Z
backVar {Γ = Γ , A} (suc x) = let
  A P., x = backVar {Γ = Γ} x in A P., S x

--

erase-Ren : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}{ρ⋆ : ⋆.Ren Φ Ψ}
  → A.Ren ρ⋆ Γ Δ → U.Ren (len Γ) (len Δ) 
erase-Ren ρ i = eraseVar (ρ (P.proj₂ (backVar i)))

--

erase-Sub : ∀{Φ Ψ}{Γ : Ctx Φ}{Δ : Ctx Ψ}{σ⋆ : SubNf Φ Ψ}
  → A.Sub σ⋆ Γ Δ → U.Sub (len Γ) (len Δ) 
erase-Sub σ i = erase (σ (P.proj₂ (backVar i)))
\end{code}
