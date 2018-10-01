\begin{code}
module Type.BetaNBE where
\end{code} where

## Imports

\begin{code}
open import Type
open import Type.BetaNormal
open import Type.RenamingSubstitution
open import Type.Equality

open import Function
open import Data.Sum
open import Data.Empty
open import Data.Product
open import Data.Unit

open import Relation.Binary.PropositionalEquality hiding ([_]; subst)
\end{code}

\begin{code}
Val : Ctx⋆ -> Kind -> Set
Val Γ  *      = Γ ⊢Nf⋆ *
Val Γ (σ ⇒ τ) = Γ ⊢NeN⋆ (σ ⇒ τ) ⊎ ∀ {Δ} -> Ren Γ Δ -> Val Δ σ -> Val Δ τ

neV : ∀{Γ σ} → Γ ⊢NeN⋆ σ → Val Γ σ
neV {σ = *}     n = ne n
neV {σ = σ ⇒ τ} n = inj₁ n

fresh : ∀ {Γ σ} -> Val (Γ ,⋆ σ) σ
fresh = neV (` Z)

renval : ∀ {σ Γ Δ} -> Ren Γ Δ -> Val Γ σ -> Val Δ σ
renval {*}     ψ n         = renameNf ψ n
renval {σ ⇒ τ} ψ (inj₁ n)  = inj₁ (renameNeN ψ n)
renval {σ ⇒ τ} ψ (inj₂ f)  = inj₂ (λ ρ' →  f (ρ' ∘ ψ))

readback : ∀ {σ Γ} -> Val Γ σ -> Γ ⊢Nf⋆ σ
readback {*}     n         = n
readback {σ ⇒ τ} (inj₁ n)  = ne n
readback {σ ⇒ τ} (inj₂ f)  = ƛ (readback (f S fresh))
\end{code}

\begin{code}
Env : Ctx⋆ → Ctx⋆ → Set
Env Δ Γ = ∀{J} → Δ ∋⋆ J → Val Γ J

_,,⋆_ : ∀{Δ Γ} → (σ : Env Γ Δ) → ∀{K}(A : Val Δ K) → Env (Γ ,⋆ K) Δ
(σ ,,⋆ A) Z = A
(σ ,,⋆ A) (S x) = σ x
\end{code}

\begin{code}
_·V_ : ∀{Γ K J} → Val Γ (K ⇒ J) → Val Γ K → Val Γ J
inj₁ n ·V v = neV (n · readback v)
inj₂ f ·V v = f id v
\end{code}

\begin{code}
eval : ∀{Γ Δ K} → Δ ⊢⋆ K → (∀{J} → Δ ∋⋆ J → Val Γ J)  → Val Γ K
eval (` x)   ρ = ρ x
eval (Π B)   ρ = Π (readback (eval B ((renval S ∘ ρ) ,,⋆ fresh)))
eval (A ⇒ B) ρ = readback (eval A ρ) ⇒ readback (eval B ρ)
eval (ƛ B)   ρ = inj₂ λ ρ' v → eval B ((renval ρ' ∘ ρ) ,,⋆ v)
eval (A · B) ρ = eval A ρ ·V eval B ρ
eval (μ B)   ρ = μ (readback (eval B ((renval S ∘ ρ) ,,⋆ fresh)))
\end{code}

\begin{code}
idEnv : ∀ Γ → Env Γ Γ
idEnv Γ = neV ∘ `
{-
idEnv ∅ ()
idEnv (Γ ,⋆ K) Z     = fresh
idEnv (Γ ,⋆ K) (S x) = renval S (idEnv Γ x)
-}
\end{code}

\begin{code}
nf : ∀{Γ K} → Γ ⊢⋆ K → Γ ⊢Nf⋆ K
nf t = readback (eval t (idEnv _))
\end{code}

