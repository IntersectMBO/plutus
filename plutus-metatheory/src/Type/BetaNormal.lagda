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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Utils using (Kind;J;K)
open Kind 
open import Type using (Ctx⋆;_,⋆_;Φ;Ψ;_⊢⋆_;_∋⋆_;S)
open _⊢⋆_
open import Type.RenamingSubstitution using (Ren;ren;ext)
import Builtin.Constant.Type as Syn
\end{code}

## Type β-normal forms

We mutually define normal forms and neutral terms. It is guaranteed
that not further beta reductions are possible. Neutral terms can be
variables, neutral applications (where the term in the function
position cannot be a lambda), or recursive types. Normal forms can be
pi types, function types, lambdas or neutral terms.

\begin{code}
data _⊢Nf⋆_ : Ctx⋆ → Kind → Set

import Builtin.Constant.Type as Nf

data _⊢Ne⋆_ : Ctx⋆ → Kind → Set where
  ` : Φ ∋⋆ J
      --------
    → Φ ⊢Ne⋆ J

  _·_ : Φ ⊢Ne⋆ (K ⇒ J)
      → Φ ⊢Nf⋆ K
        ------
      → Φ ⊢Ne⋆ J
      
  ^ : Nf.TyCon K → Φ ⊢Ne⋆ K

data _⊢Nf⋆_ where

  Π : Φ ,⋆ K ⊢Nf⋆ *
      -----------
    → Φ ⊢Nf⋆ *

  _⇒_ : Φ ⊢Nf⋆ *
      → Φ ⊢Nf⋆ *
        ------
      → Φ ⊢Nf⋆ *

  ƛ : Φ ,⋆ K ⊢Nf⋆ J
      -----------
    → Φ ⊢Nf⋆ (K ⇒ J)

  ne : Φ ⊢Ne⋆ K
       --------
     → Φ ⊢Nf⋆ K

  con : Φ ⊢Nf⋆ ♯ → Φ ⊢Nf⋆ *

  μ : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *
    → Φ ⊢Nf⋆ K
      -----------------------
    → Φ ⊢Nf⋆ *
\end{code}

# Renaming

We need to be able to weaken (introduce a new variable into the
context) in normal forms so we define renaming which subsumes
weakening.

\begin{code}
RenNf : Ctx⋆ → Ctx⋆ → Set 
RenNf Φ Ψ = ∀{J} → Φ ⊢Nf⋆ J → Ψ ⊢Nf⋆ J

RenNe : Ctx⋆ → Ctx⋆ → Set 
RenNe Φ Ψ = ∀{J} → Φ ⊢Ne⋆ J → Ψ ⊢Ne⋆ J


renNf : Ren Φ Ψ
        ---------
      → RenNf Φ Ψ
renNe : Ren Φ Ψ
        ---------
      → RenNe Φ Ψ

renNf ρ (Π A)     = Π (renNf (ext ρ) A)
renNf ρ (A ⇒ B)   = renNf ρ A ⇒ renNf ρ B
renNf ρ (ƛ B)     = ƛ (renNf (ext ρ) B)
renNf ρ (ne A)    = ne (renNe ρ A)
renNf ρ (con c)   = con (renNf ρ c)
renNf ρ (μ A B)   = μ (renNf ρ A) (renNf ρ B)

renNe ρ (` x)   = ` (ρ x)
renNe ρ (A · x) = renNe ρ A · renNf ρ x
renNe ρ (^ x)   = ^ x
\end{code}

\begin{code}
weakenNf : Φ ⊢Nf⋆ J
           -------------
         → Φ ,⋆ K ⊢Nf⋆ J
weakenNf = renNf S
\end{code}

Embedding normal forms back into terms

\begin{code}
embNf : ∀{Φ K} → Φ ⊢Nf⋆ K → Φ ⊢⋆ K
embNe : ∀{Φ K} → Φ ⊢Ne⋆ K → Φ ⊢⋆ K

embNf (Π B)   = Π (embNf B)
embNf (A ⇒ B) = embNf A ⇒ embNf B
embNf (ƛ B)    = ƛ (embNf B)
embNf (ne B)  = embNe B
embNf (con c) = con (embNf c )
embNf (μ A B) = μ (embNf A) (embNf B)

embNe (` x)   = ` x
embNe (A · B) = embNe A · embNf B
embNe (^ x)   = ^ x
\end{code}

\begin{code}
ren-embNf : (ρ : Ren Φ Ψ)
          → ∀ {J}
          → (n : Φ ⊢Nf⋆ J)
            -----------------------------------
          → embNf (renNf ρ n) ≡ ren ρ (embNf n)
ren-embNe : (ρ : Ren Φ Ψ)
          → ∀ {J}
          → (n : Φ ⊢Ne⋆ J)
            -----------------------------------
          → embNe (renNe ρ n) ≡ ren ρ (embNe n)

ren-embNf ρ (Π B)   = cong Π (ren-embNf (ext ρ) B)
ren-embNf ρ (A ⇒ B) = cong₂ _⇒_ (ren-embNf ρ A) (ren-embNf ρ B)
ren-embNf ρ (ƛ B)   = cong ƛ (ren-embNf (ext ρ) B)
ren-embNf ρ (ne n)  = ren-embNe ρ n
ren-embNf ρ (con c) = cong con (ren-embNf ρ c)
ren-embNf ρ (μ A B) = cong₂ μ (ren-embNf ρ A) (ren-embNf ρ B)

ren-embNe ρ (` x)    = refl
ren-embNe ρ (n · n') = cong₂ _·_ (ren-embNe ρ n) (ren-embNf ρ n')
ren-embNe ρ (^ x)    = refl
\end{code}
