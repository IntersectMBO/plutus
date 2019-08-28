\begin{code}
module Type.BetaNormal where
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
\begin{code}
infix  4 _⊢Nf⋆_
infix 4 _⊢Ne⋆_
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution
open import Builtin.Constant.Type

open import Relation.Binary.PropositionalEquality
  renaming (subst to substEq) using (_≡_; refl; cong; cong₂; trans; sym)
open import Function
open import Agda.Builtin.Nat
\end{code}

## Type β-normal forms

We mutually define normal forms and neutral terms. It is guaranteed
that not further beta reductions are possible. Neutral terms can be
variables, neutral applications (where the term in the function
position cannot be a lambda), or recursive types. Normal forms can be
pi types, function types, lambdas or neutral terms.

\begin{code}
open import Data.String

data _⊢Nf⋆_ : Ctx⋆ → Kind → Set

data _⊢Ne⋆_ : Ctx⋆ → Kind → Set where
  ` : ∀ {Φ J}
    → Φ ∋⋆ J
      --------
    → Φ ⊢Ne⋆ J

  _·_ : ∀{Φ K J}
    → Φ ⊢Ne⋆ (K ⇒ J)
    → Φ ⊢Nf⋆ K
      ------
    → Φ ⊢Ne⋆ J

  μ1 : ∀{φ K}
     ---------------------------------
    → φ ⊢Ne⋆ ((K ⇒ *) ⇒ K ⇒ *) ⇒ K ⇒ *

data _⊢Nf⋆_ where

  Π : ∀ {Φ K}
    → String
    → Φ ,⋆ K ⊢Nf⋆ *
      -----------
    → Φ ⊢Nf⋆ *

  _⇒_ : ∀ {Φ}
    → Φ ⊢Nf⋆ *
    → Φ ⊢Nf⋆ *
      ------
    → Φ ⊢Nf⋆ *

  ƛ :  ∀ {Φ K J}
    → String
    → Φ ,⋆ K ⊢Nf⋆ J
      -----------
    → Φ ⊢Nf⋆ (K ⇒ J)

  ne : ∀{φ K}
    → φ ⊢Ne⋆ K
      --------
    → φ ⊢Nf⋆ K

  con : ∀{φ} → TyCon → φ ⊢Nf⋆ *

\end{code}

# Renaming

We need to be able to weaken (introduce a new variable into the
context) in normal forms so we define renaming which subsumes
weakening.

\begin{code}
renNf : ∀ {Φ Ψ}
  → Ren Φ Ψ
    -----------------------------
  → (∀ {J} → Φ ⊢Nf⋆ J → Ψ ⊢Nf⋆ J)
renNe : ∀ {Φ Ψ}
  → Ren Φ Ψ
    -------------------------------
  → (∀ {J} → Φ ⊢Ne⋆ J → Ψ ⊢Ne⋆ J)

renNf ρ (Π x A)     = Π x (renNf (ext ρ) A)
renNf ρ (A ⇒ B)     = renNf ρ A ⇒ renNf ρ B
renNf ρ (ƛ x B)     = ƛ x (renNf (ext ρ) B)
renNf ρ (ne A)      = ne (renNe ρ A)
renNf ρ (con tcn)   = con tcn

renNe ρ (` x)   = ` (ρ x)
renNe ρ (A · x) = renNe ρ A · renNf ρ x
renNe ρ μ1      = μ1
\end{code}

\begin{code}
weakenNf : ∀ {Φ J K}
  → Φ ⊢Nf⋆ J
    -------------
  → Φ ,⋆ K ⊢Nf⋆ J
weakenNf = renNf S
\end{code}

\begin{code}
renNe-cong : ∀ {Φ Ψ}
  → {f g : Ren Φ Ψ}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢Ne⋆ K)
    -------------------------
  → renNe f A ≡ renNe g A

renNf-cong : ∀ {Φ Ψ}
  → {f g : Ren Φ Ψ}
  → (∀ {J}(x : Φ ∋⋆ J) → f x ≡ g x)
  → ∀{K}(A : Φ ⊢Nf⋆ K)
    ---------------------------
  → renNf f A ≡ renNf g A
renNf-cong p (Π x A)     = cong (Π x) (renNf-cong (ext-cong p) A)
renNf-cong p (A ⇒ B)     = cong₂ _⇒_ (renNf-cong p A) (renNf-cong p B)
renNf-cong p (ƛ x A)     = cong (ƛ x) (renNf-cong (ext-cong p) A)
renNf-cong p (ne A)      = cong ne (renNe-cong p A)
renNf-cong p (con tcn)   = refl

renNe-cong p (` x)   = cong ` (p x)
renNe-cong p (A · B) = cong₂ _·_ (renNe-cong p A) (renNf-cong p B)
renNe-cong p μ1      = refl
\end{code}

\begin{code}
renNf-id : ∀ {Φ}
  → ∀ {J}
  → (n : Φ ⊢Nf⋆ J)
    -----------------
  → renNf id n ≡ n

renNe-id : ∀ {Φ}
  → ∀ {J}
  → (n : Φ ⊢Ne⋆ J)
    ------------------
  → renNe id n ≡ n

renNf-id (Π x n)       =
  cong (Π x) (trans (renNf-cong ext-id n) (renNf-id n))
renNf-id (n ⇒ n')    = cong₂ _⇒_ (renNf-id n) (renNf-id n')
renNf-id (ƛ x n)       =
  cong (ƛ x) (trans (renNf-cong ext-id n) (renNf-id n))
renNf-id (ne x)      = cong ne (renNe-id x)
renNf-id (con tcn)   = refl

renNe-id (` x)    = refl
renNe-id (n · n') = cong₂ _·_ (renNe-id n) (renNf-id n')
renNe-id μ1       = refl
\end{code}

\begin{code}
renNf-comp : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J}(A : Φ ⊢Nf⋆ J)
    -------------------------------------------
  → renNf (f ∘ g) A ≡ renNf f (renNf g A)
renNe-comp : ∀{Φ Ψ Θ}
  → {g : Ren Φ Ψ}
  → {f : Ren Ψ Θ}
  → ∀{J}(A : Φ ⊢Ne⋆ J)
    -------------------------------------------
  → renNe (f ∘ g) A ≡ renNe f (renNe g A)

renNf-comp (Π x B)     =
  cong (Π x) (trans (renNf-cong ext-comp B) (renNf-comp B))
renNf-comp (A ⇒ B)     = cong₂ _⇒_ (renNf-comp A) (renNf-comp B)
renNf-comp (ƛ x B)     = 
  cong (ƛ x) (trans (renNf-cong ext-comp B) (renNf-comp B))
renNf-comp (ne n)      = cong ne (renNe-comp n)
renNf-comp (con tcn)   = refl

renNe-comp (` x) = cong ` refl
renNe-comp (A · x) = cong₂ _·_ (renNe-comp A) (renNf-comp x)
renNe-comp μ1    = refl
\end{code}

Embedding normal forms back into terms

\begin{code}
embNf : ∀{Γ K} → Γ ⊢Nf⋆ K → Γ ⊢⋆ K
embNe : ∀{Γ K} → Γ ⊢Ne⋆ K → Γ ⊢⋆ K

embNf (Π x B)     = Π x (embNf B)
embNf (A ⇒ B)     = embNf A ⇒ embNf B
embNf (ƛ x B)     = ƛ x (embNf B)
embNf (ne B)      = embNe B
embNf (con tcn)   = con tcn

embNe (` x)   = ` x
embNe (A · B) = embNe A · embNf B
embNe μ1      = μ1
\end{code}

\begin{code}
ren-embNf : ∀ {Φ Ψ}
  → (ρ : Ren Φ Ψ)
  → ∀ {J}
  → (n : Φ ⊢Nf⋆ J)
    -----------------------------------------
  → embNf (renNf ρ n) ≡ ren ρ (embNf n)

ren-embNe : ∀ {Φ Ψ}
  → (ρ : Ren Φ Ψ)
  → ∀ {J}
  → (n : Φ ⊢Ne⋆ J)
    --------------------------------------------
  → embNe (renNe ρ n) ≡ ren ρ (embNe n)

ren-embNf ρ (Π x B)     = cong (Π x) (ren-embNf (ext ρ) B)
ren-embNf ρ (A ⇒ B)     = cong₂ _⇒_ (ren-embNf ρ A) (ren-embNf ρ B)
ren-embNf ρ (ƛ x B)     = cong (ƛ x) (ren-embNf (ext ρ) B)
ren-embNf ρ (ne n)      = ren-embNe ρ n
ren-embNf ρ (con tcn  ) = refl

ren-embNe ρ (` x)    = refl
ren-embNe ρ (n · n') = cong₂ _·_ (ren-embNe ρ n) (ren-embNf ρ n')
ren-embNe ρ μ1       = refl
\end{code}

# Assemblies

\begin{code}
booleanNf : ∀{Γ} → Γ ⊢Nf⋆ *
booleanNf = Π "α" (ne (` Z) ⇒ ne (` Z) ⇒ ne (` Z))
\end{code}
