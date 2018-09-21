\begin{code}
module Type.BetaNBE where
\end{code} where

## Imports

\begin{code}
open import Type
open import Type.BetaNormal
open import Type.RenamingSubstitution

open import Function
open import Data.Sum
open import Data.Empty
\end{code}

\begin{code}
Ren : Ctx⋆ → Ctx⋆ → Set
Ren Δ Γ = ∀{J} → Δ ∋⋆ J → Γ ∋⋆ J
\end{code}

\begin{code}
mutual
  Val : Ctx⋆ -> Kind -> Set
  Val Γ σ = Γ ⊢NeN⋆ σ ⊎ Kripke Γ σ

  Kripke : Ctx⋆ -> Kind -> Set
  Kripke Γ  *      = Γ ⊢Nf⋆ *
  Kripke Γ (σ ⇒ τ) = ∀ {Δ} -> Ren Γ Δ -> Val Δ σ -> Val Δ τ

var : ∀ {Γ σ} -> Γ ∋⋆ σ -> Val Γ σ
var = inj₁ ∘ `

renval : ∀ {σ Γ Δ} -> Ren Γ Δ -> Val Γ σ -> Val Δ σ
renval         ψ (inj₁ t)  = inj₁ (renameNeN ψ t)
renval {*}     ψ (inj₂ n)  = inj₂ (renameNf ψ n)
renval {σ ⇒ τ} ψ (inj₂ k)  = inj₂ (λ ρ' →  k (ρ' ∘ ψ))

readback : ∀ {σ Γ} -> Val Γ σ -> Γ ⊢Nf⋆ σ
readback         (inj₁ t)  = ne t
readback {*}     (inj₂ t)  = t
readback {σ ⇒ τ} (inj₂ k)  = ƛ (readback (k S (var Z)))
\end{code}

\begin{code}
Env : Ctx⋆ → Ctx⋆ → Set
Env Δ Γ = ∀{J} → Δ ∋⋆ J → Val Γ J

_,,⋆_ : ∀{Δ Γ} → (σ : Env Γ Δ) → ∀{K}(A : Val Δ K) → Env (Γ ,⋆ K) Δ
(σ ,,⋆ A) Z = A
(σ ,,⋆ A) (S x) = σ x
\end{code}

\begin{code}
eval : ∀{Γ Δ K} → Δ ⊢⋆ K → (∀{J} → Δ ∋⋆ J → Val Γ J)  → Val Γ K
eval (` x)   ρ = ρ x
eval (Π B)   ρ = inj₂ (Π (readback (eval B ((renval S ∘ ρ) ,,⋆ var Z))))
eval (A ⇒ B) ρ = inj₂ (readback (eval A ρ) ⇒ readback (eval B ρ))
eval (ƛ B)   ρ = inj₂ λ ρ' v → eval B ((renval ρ' ∘ ρ) ,,⋆ v)
eval (A · B) ρ with eval A ρ
eval (A · B) ρ | inj₁ n = inj₁ (n · readback (eval B ρ))
eval (A · B) ρ | inj₂ f = f id (eval B ρ) 
eval (μ B)   ρ = inj₂ (μ (readback (eval B ((renval S ∘ ρ) ,,⋆ var Z))))
\end{code}

\begin{code}
idEnv : ∀ Γ → Env Γ Γ
idEnv ∅ ()
idEnv (Γ ,⋆ K) Z     = var Z
idEnv (Γ ,⋆ K) (S x) = renval S (idEnv Γ x)
\end{code}

\begin{code}
nf : ∀{Γ K} → Γ ⊢⋆ K → Γ ⊢Nf⋆ K
nf t = readback (eval t (idEnv _))
\end{code}

\begin{code}
_[_]Nf : ∀ {Φ J K}
        → Φ ,⋆ K ⊢Nf⋆ J
        → Φ ⊢Nf⋆ K 
          ------
        → Φ ⊢Nf⋆ J
A [ B ]Nf = nf (embNf A [ embNf B ])
\end{code}

