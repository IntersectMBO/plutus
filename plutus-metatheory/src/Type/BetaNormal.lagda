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
open import Utils
open import Type
open import Type.RenamingSubstitution
import Builtin.Constant.Type Ctx⋆ (_⊢⋆ *) as Syn


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
data _⊢Nf⋆_ : Ctx⋆ → Kind → Set

import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) as Nf

data _⊢Ne⋆_ : Ctx⋆ → Kind → Set where
  ` : Φ ∋⋆ J
      --------
    → Φ ⊢Ne⋆ J

  _·_ : Φ ⊢Ne⋆ (K ⇒ J)
      → Φ ⊢Nf⋆ K
        ------
      → Φ ⊢Ne⋆ J

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

  con : Nf.TyCon Φ → Φ ⊢Nf⋆ *

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

RenNfTyCon : Ctx⋆ → Ctx⋆ → Set 
RenNfTyCon Φ Ψ = Nf.TyCon Φ → Nf.TyCon Ψ


RenNe : Ctx⋆ → Ctx⋆ → Set 
RenNe Φ Ψ = ∀{J} → Φ ⊢Ne⋆ J → Ψ ⊢Ne⋆ J


renNf : Ren Φ Ψ
        ---------
      → RenNf Φ Ψ

renNfTyCon : Ren Φ Ψ
        ---------
      → RenNfTyCon Φ Ψ

renNe : Ren Φ Ψ
        ---------
      → RenNe Φ Ψ

renNfTyCon ρ Nf.integer    = Nf.integer
renNfTyCon ρ Nf.bytestring = Nf.bytestring
renNfTyCon ρ Nf.string     = Nf.string
renNfTyCon ρ Nf.unit       = Nf.unit
renNfTyCon ρ Nf.bool       = Nf.bool
renNfTyCon ρ (Nf.list A)   = Nf.list (renNf ρ A)
renNfTyCon ρ (Nf.pair A B) = Nf.pair (renNf ρ A) (renNf ρ B)
renNfTyCon ρ Nf.Data       = Nf.Data

renNf ρ (Π A)     = Π (renNf (ext ρ) A)
renNf ρ (A ⇒ B)   = renNf ρ A ⇒ renNf ρ B
renNf ρ (ƛ B)     = ƛ (renNf (ext ρ) B)
renNf ρ (ne A)    = ne (renNe ρ A)
renNf ρ (con c)   = con (renNfTyCon ρ c)
renNf ρ (μ A B)   = μ (renNf ρ A) (renNf ρ B)

renNe ρ (` x)   = ` (ρ x)
renNe ρ (A · x) = renNe ρ A · renNf ρ x
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
embNfTyCon : ∀{Φ} → Nf.TyCon Φ → Syn.TyCon Φ

embNfTyCon Nf.integer = Syn.integer
embNfTyCon Nf.bytestring = Syn.bytestring
embNfTyCon Nf.string = Syn.string
embNfTyCon Nf.unit = Syn.unit
embNfTyCon Nf.bool = Syn.bool
embNfTyCon (Nf.list A) = Syn.list (embNf A)
embNfTyCon (Nf.pair A B) = Syn.pair (embNf A) (embNf B)
embNfTyCon Nf.Data = Syn.Data

embNf (Π B)   = Π (embNf B)
embNf (A ⇒ B) = embNf A ⇒ embNf B
embNf (ƛ B)    = ƛ (embNf B)
embNf (ne B)  = embNe B
embNf (con c) = con (embNfTyCon c )
embNf (μ A B) = μ (embNf A) (embNf B)

embNe (` x)   = ` x
embNe (A · B) = embNe A · embNf B
\end{code}

\begin{code}
ren-embNf : (ρ : Ren Φ Ψ)
          → ∀ {J}
          → (n : Φ ⊢Nf⋆ J)
            -----------------------------------
          → embNf (renNf ρ n) ≡ ren ρ (embNf n)

renTyCon-embNf : (ρ : Ren Φ Ψ)
               → (c : Nf.TyCon Φ)
                 -----------------------------------
               → embNfTyCon (renNfTyCon ρ c) ≡ renTyCon ρ (embNfTyCon c)

renTyCon-embNf ρ Nf.integer = refl
renTyCon-embNf ρ Nf.bytestring = refl
renTyCon-embNf ρ Nf.string = refl
renTyCon-embNf ρ Nf.unit = refl
renTyCon-embNf ρ Nf.bool = refl
renTyCon-embNf ρ (Nf.list A) = cong Syn.list (ren-embNf ρ A)
renTyCon-embNf ρ (Nf.pair A B) = cong₂ Syn.pair (ren-embNf ρ A) (ren-embNf ρ B)
renTyCon-embNf ρ Nf.Data = refl

ren-embNe : (ρ : Ren Φ Ψ)
          → ∀ {J}
          → (n : Φ ⊢Ne⋆ J)
            -----------------------------------
          → embNe (renNe ρ n) ≡ ren ρ (embNe n)

ren-embNf ρ (Π B)   = cong Π (ren-embNf (ext ρ) B)
ren-embNf ρ (A ⇒ B) = cong₂ _⇒_ (ren-embNf ρ A) (ren-embNf ρ B)
ren-embNf ρ (ƛ B)   = cong ƛ (ren-embNf (ext ρ) B)
ren-embNf ρ (ne n)  = ren-embNe ρ n
ren-embNf ρ (con c) = cong con (renTyCon-embNf ρ c)
ren-embNf ρ (μ A B) = cong₂ μ (ren-embNf ρ A) (ren-embNf ρ B)

ren-embNe ρ (` x)    = refl
ren-embNe ρ (n · n') = cong₂ _·_ (ren-embNe ρ n) (ren-embNf ρ n')
\end{code}
