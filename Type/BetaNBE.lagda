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

Values are defined by induction on kind. At kind size and * they are
inert and defined to be just normal forms. At function kind they are
either neutral or Kripke functions

\begin{code}
Val : Ctx⋆ -> Kind -> Set
Val Γ size    = Γ ⊢Nf⋆ size
Val Γ  *      = Γ ⊢Nf⋆ *
Val Γ (σ ⇒ τ) = Γ ⊢NeN⋆ (σ ⇒ τ) ⊎ ∀ {Δ} -> Ren Γ Δ -> Val Δ σ -> Val Δ τ
\end{code}

We can embed neutral terms into values at any kind using reflect.
reflect is quite simple in this version of NBE and not mutually
defined with reify.

\begin{code}
reflect : ∀{Γ σ} → Γ ⊢NeN⋆ σ → Val Γ σ
reflect {σ = size}  n = ne n
reflect {σ = *}     n = ne n
reflect {σ = σ ⇒ τ} n = inj₁ n
\end{code}

A shorthand for creating a new fresh variable as a value which we need
in reify

\begin{code}
fresh : ∀ {Γ σ} -> Val (Γ ,⋆ σ) σ
fresh = reflect (` Z)
\end{code}

Renaming for values

\begin{code}
renval : ∀ {σ Γ Δ} -> Ren Γ Δ -> Val Γ σ -> Val Δ σ
renval {size}  ψ n         = renameNf ψ n
renval {*}     ψ n         = renameNf ψ n
renval {σ ⇒ τ} ψ (inj₁ n)  = inj₁ (renameNeN ψ n)
renval {σ ⇒ τ} ψ (inj₂ f)  = inj₂ (λ ρ' →  f (ρ' ∘ ψ))
\end{code}

Reify takes a value and yields a normal form.

\begin{code}
reify : ∀ {σ Γ} -> Val Γ σ -> Γ ⊢Nf⋆ σ
reify {size}  n         = n
reify {*}     n         = n
reify {σ ⇒ τ} (inj₁ n)  = ne n
reify {σ ⇒ τ} (inj₂ f)  = ƛ (reify (f S fresh))
\end{code}

An environment is a mapping from variables to values

\begin{code}
Env : Ctx⋆ → Ctx⋆ → Set
Env Δ Γ = ∀{J} → Δ ∋⋆ J → Val Γ J
\end{code}

'cons' for environments

\begin{code}
_,,⋆_ : ∀{Δ Γ} → (σ : Env Γ Δ) → ∀{K}(A : Val Δ K) → Env (Γ ,⋆ K) Δ
(σ ,,⋆ A) Z = A
(σ ,,⋆ A) (S x) = σ x
\end{code}

Application for values. As values at function type can be semantic
functions or neutral terms we need this function to unpack them. If
the function is neutral we create a neutral application by reifying
the value and applying the neutral application constructor, then we
refect the neutral application into a value. If the function is a
semantic function we apply it to the identity renaming and then to
the argument. In this case, the function and argument are in the same
context so we do not need the Kripke extension, hence the identity
renaming.

\begin{code}
_·V_ : ∀{Γ K J} → Val Γ (K ⇒ J) → Val Γ K → Val Γ J
inj₁ n ·V v = reflect (n · reify v)
inj₂ f ·V v = f id v
\end{code}

Evaluation a term in an environment yields a value.

\begin{code}
eval : ∀{Γ Δ K} → Δ ⊢⋆ K → (∀{J} → Δ ∋⋆ J → Val Γ J)  → Val Γ K
eval (` x)   ρ = ρ x
eval (Π B)   ρ = Π (reify (eval B ((renval S ∘ ρ) ,,⋆ fresh)))
eval (A ⇒ B) ρ = reify (eval A ρ) ⇒ reify (eval B ρ)
eval (ƛ B)   ρ = inj₂ λ ρ' v → eval B ((renval ρ' ∘ ρ) ,,⋆ v)
eval (A · B) ρ = eval A ρ ·V eval B ρ
eval (μ B)   ρ = reflect (μ (reify (eval B ((renval S ∘ ρ) ,,⋆ fresh))))
\end{code}

Identity environment

\begin{code}
idEnv : ∀ Γ → Env Γ Γ
idEnv Γ = reflect ∘ `
\end{code}

Normalisation a term yields a normal form. We evaluate in the identity
environment to yield a value in the same context as the original term
and then reify to yield a normal form

\begin{code}
nf : ∀{Γ K} → Γ ⊢⋆ K → Γ ⊢Nf⋆ K
nf t = reify (eval t (idEnv _))
\end{code}
