\begin{code}
module Type.BetaNBE where
\end{code}

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
open import Data.String

open import Relation.Binary.PropositionalEquality hiding ([_]; subst)
\end{code}

Values are defined by induction on kind. At kind # and * they are
inert and defined to be just normal forms. At function kind they are
either neutral or Kripke functions

\begin{code}
Val : Ctx⋆ → Kind → Set
Val Φ *       = Φ ⊢Nf⋆ *
Val Φ (σ ⇒ τ) = Φ ⊢Ne⋆ (σ ⇒ τ) ⊎ ∀ {Ψ} → Ren Φ Ψ → Val Ψ σ → Val Ψ τ
\end{code}

We can embed neutral terms into values at any kind using reflect.
reflect is quite simple in this version of NBE and not mutually
defined with reify.

\begin{code}
reflect : ∀{Φ σ} → Φ ⊢Ne⋆ σ → Val Φ σ
reflect {σ = *}     n = ne n
reflect {σ = σ ⇒ τ} n = inj₁ n
\end{code}

A shorthand for creating a new fresh variable as a value which we need
in reify

\begin{code}
fresh : ∀ {Φ σ} → Val (Φ ,⋆ σ) σ
fresh = reflect (` Z)
\end{code}

Renaming for values

\begin{code}
renVal : ∀ {σ Φ Ψ} → Ren Φ Ψ → Val Φ σ → Val Ψ σ
renVal {*}     ψ n        = renNf ψ n
renVal {σ ⇒ τ} ψ (inj₁ n) = inj₁ (renNe ψ n)
renVal {σ ⇒ τ} ψ (inj₂ f) = inj₂ λ ρ' →  f (ρ' ∘ ψ)
\end{code}

Weakening for values

\begin{code}
weakenVal : ∀ {σ Φ K} → Val Φ σ → Val (Φ ,⋆ K) σ
weakenVal = renVal S
\end{code}

Reify takes a value and yields a normal form.

\begin{code}
reify : ∀ {σ Φ} → Val Φ σ → Φ ⊢Nf⋆ σ
reify {*}     n         = n
reify {σ ⇒ τ} (inj₁ n)  = ne n
reify {σ ⇒ τ} (inj₂ f)  = ƛ (reify (f S fresh)) -- has a name been lost here?
\end{code}

An environment is a mapping from variables to values

\begin{code}
Env : Ctx⋆ → Ctx⋆ → Set
Env Ψ Φ = ∀{J} → Ψ ∋⋆ J → Val Φ J
\end{code}

'cons' for environments

\begin{code}
_,,⋆_ : ∀{Ψ Φ} → (σ : Env Φ Ψ) → ∀{K}(A : Val Ψ K) → Env (Φ ,⋆ K) Ψ
(σ ,,⋆ A) Z     = A
(σ ,,⋆ A) (S α) = σ α
\end{code}

\begin{code}
exte : ∀ {Φ Ψ} → Env Φ Ψ → (∀ {K} → Env (Φ ,⋆ K) (Ψ ,⋆ K))
exte η = (weakenVal ∘ η) ,,⋆ fresh
{-
-- this version would be more analogous to ext and exts but would
-- require changing some proofs for terms
exte η Z      = fresh
exte η (S α)  = weakenVal (η α)
-}
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
_·V_ : ∀{Φ K J} → Val Φ (K ⇒ J) → Val Φ K → Val Φ J
inj₁ n ·V v = reflect (n · reify v)
inj₂ f ·V v = f id v
\end{code}

Evaluation a term in an environment yields a value. The most
interesting cases are ƛ where we introduce a new Kripke function that
will evaluate when it receives an argument and Π/μ where we need to go
under the binder and extend the environement before evaluating and
reifying.

\begin{code}
eval : ∀{Φ Ψ K} → Ψ ⊢⋆ K → Env Ψ Φ → Val Φ K
eval (` α)       η = η α
eval (Π B)       η = Π (reify (eval B (exte η)))
eval (A ⇒ B)     η = reify (eval A η) ⇒ reify (eval B η)
eval (ƛ B)       η = inj₂ λ ρ v → eval B ((renVal ρ ∘ η) ,,⋆ v)
eval (A · B)     η = eval A η ·V eval B η
eval (μ A B)     η = μ (reify (eval A η)) (reify (eval B η))
eval (con tcn)   η = con tcn
\end{code}

Identity environment

\begin{code}
idEnv : ∀ Φ → Env Φ Φ
idEnv Φ = reflect ∘ `
\end{code}

Normalisating a term yields a normal form. We evaluate in the identity
environment to yield a value in the same context as the original term
and then reify to yield a normal form

\begin{code}
nf : ∀{Φ K} → Φ ⊢⋆ K → Φ ⊢Nf⋆ K
nf t = reify (eval t (idEnv _))
\end{code}
