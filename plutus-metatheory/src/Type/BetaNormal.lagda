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
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec;[];_∷_) 
open import Data.List using (List;[];_∷_)
open import Data.Product using (Σ;Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Utils using (Kind;J;K)
open Kind 
open import Type using (Ctx⋆;_,⋆_;Φ;Ψ;_⊢⋆_;_∋⋆_;S)
open _⊢⋆_
open import Type.RenamingSubstitution using (Ren;ren;ext;ren-List;ren-VecList)
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

  SOP : ∀{n} →   -- n cases
        Vec (List (Φ ⊢Nf⋆ *)) n
        ---------------------------------------------
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
renNf-List : Ren Φ Ψ →  ∀{J} → List (Φ ⊢Nf⋆ J) → List (Ψ ⊢Nf⋆ J)
renNf-VecList : ∀{n} → Ren Φ Ψ →  ∀{J} → Vec (List (Φ ⊢Nf⋆ J)) n → Vec (List (Ψ ⊢Nf⋆ J)) n

renNf ρ (Π A)     = Π (renNf (ext ρ) A)
renNf ρ (A ⇒ B)   = renNf ρ A ⇒ renNf ρ B
renNf ρ (ƛ B)     = ƛ (renNf (ext ρ) B)
renNf ρ (ne A)    = ne (renNe ρ A)
renNf ρ (con c)   = con (renNf ρ c)
renNf ρ (μ A B)   = μ (renNf ρ A) (renNf ρ B)
renNf ρ (SOP xss) = SOP (renNf-VecList ρ xss)

renNf-List ρ [] = []
renNf-List ρ (x ∷ xs) = renNf ρ x ∷ renNf-List ρ xs
renNf-VecList ρ [] = []
renNf-VecList ρ (xs ∷ xss) = renNf-List ρ xs ∷ renNf-VecList ρ xss

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
embNf-List : ∀{Φ K} → List (Φ ⊢Nf⋆ K) → List (Φ ⊢⋆ K)
embNf-VecList : ∀{n Φ K} → Vec (List (Φ ⊢Nf⋆ K)) n → Vec (List (Φ ⊢⋆ K)) n

embNf (Π B)     = Π (embNf B)
embNf (A ⇒ B)   = embNf A ⇒ embNf B
embNf (ƛ B)     = ƛ (embNf B)
embNf (ne B)    = embNe B
embNf (con c)   = con (embNf c )
embNf (μ A B)   = μ (embNf A) (embNf B)
embNf (SOP xss) = SOP (embNf-VecList xss)

embNe (` x)   = ` x
embNe (A · B) = embNe A · embNf B
embNe (^ x)   = ^ x

embNf-List [] = []
embNf-List (x ∷ xs) = embNf x ∷ embNf-List xs
embNf-VecList [] = []
embNf-VecList (xs ∷ xss) = embNf-List xs ∷ embNf-VecList xss

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
ren-embNf-List : ∀ (ρ : Ren Φ Ψ) {J}
            (xss : List (Φ ⊢Nf⋆ J))
            -------------------------------------------------------------------
          → embNf-List (renNf-List ρ xss) ≡ ren-List ρ (embNf-List xss)

ren-embNf-VecList : ∀ (ρ : Ren Φ Ψ) {n} {J}
            (xss : Vec (List (Φ ⊢Nf⋆ J)) n)
            -------------------------------------------------------------------
          → embNf-VecList (renNf-VecList ρ xss) ≡ ren-VecList ρ (embNf-VecList xss)


ren-embNf ρ (Π B)     = cong Π (ren-embNf (ext ρ) B)
ren-embNf ρ (A ⇒ B)   = cong₂ _⇒_ (ren-embNf ρ A) (ren-embNf ρ B)
ren-embNf ρ (ƛ B)     = cong ƛ (ren-embNf (ext ρ) B)
ren-embNf ρ (ne n)    = ren-embNe ρ n
ren-embNf ρ (con c)   = cong con (ren-embNf ρ c)
ren-embNf ρ (μ A B)   = cong₂ μ (ren-embNf ρ A) (ren-embNf ρ B)
ren-embNf ρ (SOP xss) = cong SOP (ren-embNf-VecList ρ xss)

ren-embNe ρ (` x)    = refl
ren-embNe ρ (n · n') = cong₂ _·_ (ren-embNe ρ n) (ren-embNf ρ n')
ren-embNe ρ (^ x)    = refl

ren-embNf-List ρ [] = refl
ren-embNf-List ρ (x ∷ xs) = cong₂ _∷_ (ren-embNf ρ x) (ren-embNf-List ρ xs)
ren-embNf-VecList ρ [] = refl
ren-embNf-VecList ρ (xs ∷ xss) = cong₂ _∷_ (ren-embNf-List ρ xs) (ren-embNf-VecList ρ xss)
\end{code}

Some properties relating uses of lookup on VecList-functions with List-functions

\begin{code}
module _ where

  open import Data.Fin using (Fin;zero;suc)
  open import Data.Vec using (lookup)
  
  lookup-renNf-VecList : ∀ {Φ Ψ n}
              → (ρ⋆ : Ren Φ Ψ)
              → (e : Fin n)
              → (A : Vec (List (Φ ⊢Nf⋆ *)) n)
                --------------------------------------------
              → lookup (renNf-VecList ρ⋆ A) e ≡ renNf-List ρ⋆ (lookup A e)
  lookup-renNf-VecList ρ⋆ zero (x ∷ A) = refl
  lookup-renNf-VecList ρ⋆ (suc e) (_ ∷ A) = lookup-renNf-VecList ρ⋆ e A

  lookup-embNf-VecList : ∀ {n}
              → (e : Fin n)
              → (A : Vec (List (Φ ⊢Nf⋆ *)) n)
                --------------------------------------------
              → lookup (embNf-VecList A) e ≡ embNf-List (lookup A e)
  lookup-embNf-VecList zero (x ∷ A) = refl
  lookup-embNf-VecList (suc e) (x ∷ A) = lookup-embNf-VecList e A
\end{code}

