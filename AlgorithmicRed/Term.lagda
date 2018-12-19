\begin{code}
module AlgorithmicRed.Term where
\end{code}

## Imports

\begin{code}
open import Function hiding (_∋_)



open import Type
open import Type.RenamingSubstitution
open import Type.BetaNormal

booleanNf : ∀{Γ} → Γ ⊢Nf⋆ *
booleanNf = Π (ne (` Z) ⇒ ne (` Z) ⇒ ne (` Z))

open import Type.BetaNBE
open import Builtin
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * # _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf size⋆
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢Nf⋆_ con size⋆
open import Data.Product renaming (_,_ to _,,_)
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _∋_
infix  4 _⊢_
infixl 5 _,_
\end{code}

## Contexts and erasure

We need to mutually define contexts and their
erasure to type contexts.
\begin{code}
data Ctx : Set
∥_∥ : Ctx → Ctx⋆
\end{code}

A context is either empty, or extends a context by
a type variable of a given kind, or extends a context
by a variable of a given type.
\begin{code}
data Ctx where
  ∅ : Ctx
  _,⋆_ : Ctx → Kind → Ctx
  _,_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢Nf⋆ J → Ctx
\end{code}
Let `Γ` range over contexts.  In the last rule,
the type is indexed by the erasure of the previous
context to a type context and a kind.

The erasure of a context is a type context.
\begin{code}
∥ ∅ ∥       =  ∅
∥ Γ ,⋆ J ∥  =  ∥ Γ ∥ ,⋆ J
∥ Γ , A ∥   =  ∥ Γ ∥
\end{code}

## Variables

A variable is indexed by its context and type.
\begin{code}
data _∋_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢Nf⋆ J → Set where

  Z : ∀ {Γ J} {A : ∥ Γ ∥ ⊢Nf⋆ J}
      ----------
    → Γ , A ∋ A

  S : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢Nf⋆ J} {B : ∥ Γ ∥ ⊢Nf⋆ K}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢Nf⋆ J}
    → Γ ∋ A
      -------------------
    → Γ ,⋆ K ∋ weakenNf A
\end{code}
Let `x`, `y` range over variables.



## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.
\begin{code}



postulate _—Nf→⋆_ : ∀{Γ K} → Γ ⊢⋆ K → Γ ⊢Nf⋆ K → Set
infix 4 _—Nf→⋆_

-- Tel : ∀ Γ Δ → (∀ {J} → Δ ∋⋆ J → ∥ Γ ∥ ⊢Nf⋆ J) → List (Δ ⊢Nf⋆ *) → Set

data _⊢_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢Nf⋆ J → Set where

  ` : ∀ {Γ J} {A : ∥ Γ ∥ ⊢Nf⋆ J}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ : ∀ {Γ A B}
    → Γ , A ⊢ B
      -----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ : ∀ {Γ K}
    → {B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π B

  _·⋆_ : ∀ {Γ K}
    → {B : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ *}
    → Γ ⊢ Π B
    → (A : ∥ Γ ∥ ⊢Nf⋆ K)
    → {R : ∥ Γ ∥ ⊢Nf⋆ *}
    → embNf B [ embNf A ] —Nf→⋆ R
      ---------------
    → Γ ⊢ R

  wrap1 : ∀{Γ K}
   → (pat : ∥ Γ ∥ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (arg : ∥ Γ ∥ ⊢Nf⋆ K)
   → (term : Γ ⊢ nf (embNf pat · (μ1 · embNf pat) · embNf arg))
   → Γ ⊢ ne (μ1 · pat · arg)

  unwrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢Nf⋆ K}
    → (term : Γ ⊢ ne (μ1 · pat · arg))
    → Γ ⊢ nf (embNf pat · (μ1 · embNf pat) · embNf arg)

  con : ∀{Γ s tcn}
    → TermCon (con tcn s)
      -------------------
    → Γ ⊢ con tcn s
{-
  builtin : ∀{Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {J} → Δ ∋⋆ J → ∥ Γ ∥ ⊢Nf⋆ J)
    → Tel Γ Δ σ As
      ----------------------------------
    → Γ ⊢ substNf σ C
-}
  error : ∀{Γ} → (A : ∥ Γ ∥ ⊢Nf⋆ *) → Γ ⊢ A
{-
Tel Γ Δ σ [] = ⊤
Tel Γ Δ σ (A ∷ As) = Γ ⊢ substNf σ A × Tel Γ Δ σ As
-}
\end{code}

# Term Abbreviations
\begin{code}
--void : ∀{Γ} → Γ ⊢ unitNf
--void = Λ (ƛ (` Z))

true : ∀{Γ} → Γ ⊢ booleanNf
true = Λ (ƛ (ƛ (` (S Z))))

false : ∀{Γ} → Γ ⊢ booleanNf
false = Λ (ƛ (ƛ (` Z)))
\end{code}
