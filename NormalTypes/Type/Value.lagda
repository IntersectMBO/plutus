\begin{code}
module Type.Value where
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _⊢V⋆_
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution
\end{code}

## Type Values

\begin{code}

-- data Env⋆ (Δ : Ctx⋆) : Ctx⋆ → Set
data _⊢V⋆_ : Ctx⋆ → Kind → Set

{-
data Env⋆ Δ where
  e    : Env⋆ Δ ∅
  _,⋆_ : ∀{Γ} → (σ : Env⋆ Δ Γ) → ∀{K}(A : Δ ⊢V⋆ K) → Env⋆ Δ (Γ ,⋆ K)
-}

Env⋆  = λ Δ Γ → ∀ {J} → Γ ∋⋆ J → Δ ⊢V⋆ J

data _⊢Ne⋆_ : Ctx⋆ → Kind → Set where
  `_ : ∀ {Φ J}
    → Φ ∋⋆ J
      --------
    → Φ ⊢Ne⋆ J

  _·_ : ∀{Φ K J}
    → Φ ⊢Ne⋆ (K ⇒ J)
    → Φ ⊢V⋆ K
      ------
    → Φ ⊢Ne⋆ J


data _⊢V⋆_ where

  Π : ∀ {Φ Ψ K}
    → Ψ ,⋆ K ⊢⋆ *
    → Env⋆ Φ Ψ
      -----------
    → Φ ⊢V⋆ *

  _⇒_ : ∀ {Φ}
    → Φ ⊢V⋆ *
    → Φ ⊢V⋆ *
      ------
    → Φ ⊢V⋆ *

  ƛ :  ∀ {Φ Ψ K J}
    → Ψ ,⋆ K ⊢⋆ J
    → Env⋆ Φ Ψ
      -----------
    → Φ ⊢V⋆ (K ⇒ J)

  μ : ∀{φ Ψ K}
    → Ψ ,⋆ K ⊢⋆ *
    → Env⋆ φ Ψ
      -----------
    → φ ⊢V⋆ *

  ne : ∀{φ K}
    → φ  ⊢Ne⋆ K
      -----------
    → φ ⊢V⋆ K
\end{code}

\begin{code}
{-
lookup⋆ : ∀{Δ Γ} → Env⋆ Δ Γ → ∀ {J} → Γ ∋⋆ J → Δ ⊢V⋆ J
lookup⋆ (σ ,⋆ A) Z = A
lookup⋆ (σ ,⋆ A) (S x) = lookup⋆ σ x
-}
vcons : ∀{Γ Δ} → (σ : Env⋆ Δ Γ) → ∀{K}(A : Δ ⊢V⋆ K) → Env⋆ Δ (Γ ,⋆ K)
vcons σ A Z     = A
vcons σ A (S x) = σ x
\end{code}

\begin{code}
{-# TERMINATING #-}
eval : ∀{Ψ φ J} → Ψ ⊢⋆ J → Env⋆ φ Ψ → φ ⊢V⋆ J
_·V_ : ∀{φ J K} → φ ⊢V⋆ (J ⇒ K) → φ ⊢V⋆ J → φ ⊢V⋆ K
eval (` x)   vs = vs x
eval (Π t)   vs = Π t vs
eval (t ⇒ u) vs = eval t vs ⇒ eval u vs
eval (t · u) vs = eval t vs ·V eval u vs
eval (μ t)   vs = μ t vs
eval (ƛ t)   vs = ƛ t vs

ƛ t vs ·V v = eval t (vcons vs v) 
ne n   ·V v = ne (n · v)
\end{code}

\begin{code}
renameNe : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → (∀ {J} → Φ ⊢Ne⋆ J → Ψ ⊢Ne⋆ J)

renameEnv : ∀{Φ Ψ Θ}
  (f : ∀ {J} → Ψ ∋⋆ J → Θ ∋⋆ J)(g : ∀ {J} → Φ ∋⋆ J → Ψ ⊢V⋆ J)
  → ∀ {J} → Φ ∋⋆ J → Θ ⊢V⋆ J


renameV : ∀ {Φ Ψ}
  → (∀ {J} → Φ ∋⋆ J → Ψ ∋⋆ J)
    ----------------------------
  → (∀ {J} → Φ ⊢V⋆ J → Ψ ⊢V⋆ J)
renameV ρ (Π B vs) = Π B (renameEnv ρ vs)
renameV ρ (A ⇒ B)  = renameV ρ A ⇒ renameV ρ B
renameV ρ (ƛ B vs) = ƛ B (renameEnv ρ vs)
renameV ρ (μ B vs) = μ B (renameEnv ρ vs)
renameV ρ (ne n)   = ne (renameNe ρ n)

renameNe ρ (` x) = ` (ρ x)
renameNe ρ (n · v) = renameNe ρ n · renameV ρ v

renameEnv g f x     = renameV g (f x)
\end{code}

\begin{code}
weakenV : ∀ {Φ J K}
  → Φ ⊢V⋆ J
    -------------
  → Φ ,⋆ K ⊢V⋆ J
weakenV = renameV S_
\end{code}

\begin{code}
weakenEnv : ∀ {Φ K ψ}
  → Env⋆ Φ  ψ
    -------------
  → Env⋆ (Φ ,⋆ K) ψ
weakenEnv = renameEnv S_
\end{code}

\begin{code}
extEnv : ∀ {Φ Ψ} → (∀ {J} → Φ ∋⋆ J → Ψ ⊢V⋆ J)
    ------------------------------------------
  → (∀ {J K} → Φ ,⋆ K ∋⋆ J → Ψ ,⋆ K ⊢V⋆ J)
extEnv ρ Z      =  ne (` Z)
extEnv ρ (S α)  =  renameV S_ (ρ α)
\end{code}
