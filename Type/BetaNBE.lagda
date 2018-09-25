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

open import Relation.Binary.PropositionalEquality hiding ([_])
\end{code}

\begin{code}
Ren : Ctx⋆ → Ctx⋆ → Set
Ren Δ Γ = ∀{J} → Δ ∋⋆ J → Γ ∋⋆ J
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
eval (A · B) ρ with eval A ρ
eval (A · B) ρ | inj₁ n = neV (n · readback (eval B ρ))
eval (A · B) ρ | inj₂ f = f id (eval B ρ) 
eval (μ B)   ρ = μ (readback (eval B ((renval S ∘ ρ) ,,⋆ fresh)))
\end{code}

\begin{code}
idEnv : ∀ Γ → Env Γ Γ
idEnv ∅ ()
idEnv (Γ ,⋆ K) Z     = fresh
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

## Proofs

\begin{code}
-- A Partial equivalence relation on values: 'equality on values'
PER : ∀{Γ} K → Val Γ K → Val Γ K → Set
PER *       v v' = readback v ≡ readback v'
PER (K ⇒ J) f f' = ∀{Δ}
 → (ρ : Ren _ Δ)
 → {v v' : Val Δ K}
 → PER K v v'
 → PER J (renval ρ f ·V v) (renval ρ f' ·V v')

symPER : ∀{Γ} K {v v' : Val Γ K} → PER K v v' → PER K v' v
symPER *       p = sym p
symPER (K ⇒ J) p = λ ρ q → symPER J (p ρ (symPER K q))

transPER : ∀{Γ} K {v v' v'' : Val Γ K} → PER K v v' → PER K v' v'' → PER K v v''
transPER * p q = trans p q
transPER (K ⇒ J) p q = λ ρ r
  → transPER J (p ρ r) (q ρ (transPER K (symPER K r) r))

reflPER : ∀{Γ} K {v v' : Val Γ K} → PER K v v' → PER K v v
reflPER K p = transPER K p (symPER K p)

{-
mutual
  reifyPER : ∀{Γ} K {v v' : Val Γ K}
    → PER K v v'
    → readback v ≡ readback v'
  reifyPER *       p = p
  reifyPER (K ⇒ J) p = {!!} --cong ƛ (reifyPER J (p S (reflectPER K (refl {x = ` Z})))) 
-}
\end{code}

\begin{code}
{-
rename-eval : ∀{Γ Δ Θ K}
  (t : Δ ⊢⋆ K)
  (η : ∀{J} → Δ ∋⋆ J → Val Γ J)
  (ρ : Ren Γ Θ) →
  renval ρ (eval t η) ≡ eval t (renval ρ ∘ η)
rename-eval = {!!}
-}
\end{code}

rename-eval : 

\begin{code}
{-
rename[]Nf : ∀ {Φ Θ J K}
        → (ρ : Ren Φ Θ)
        → (t : Φ ,⋆ K ⊢Nf⋆ J)
        → (u : Φ ⊢Nf⋆ K )
          ------
        → renameNf ρ (t [ u ]Nf) ≡ renameNf (ext ρ) t [ renameNf ρ u ]Nf
rename[]Nf ρ (Π B)   u = cong Π {!!}
rename[]Nf ρ (A ⇒ B) u = {!!}
rename[]Nf ρ (ƛ B)   u = {!!}
rename[]Nf ρ (μ B)   u = {!!}
rename[]Nf ρ (ne xn) u = {!!}
-}
\end{code}
