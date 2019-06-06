\begin{code}
module Algorithmic where
\end{code}

## Imports

\begin{code}
open import Function hiding (_∋_)



open import Type
open import Type.BetaNormal

open import Type.BetaNBE
open import Type.BetaNBE.RenamingSubstitution renaming (_[_]Nf to _[_])
open import Builtin
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con booleanNf 
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con 
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
--data Ctx : Set
--∥_∥ : Ctx → Ctx⋆
\end{code}

A context is either empty, or extends a context by
a type variable of a given kind, or extends a context
by a variable of a given type.
\begin{code}
data Ctx : Ctx⋆ → Set where
  ∅    : Ctx ∅
  _,⋆_ : ∀{Φ} → Ctx Φ → (J : Kind) → Ctx (Φ ,⋆ J)
  _,_  : ∀ {Φ J} (Γ : Ctx Φ) → Φ ⊢Nf⋆ J → Ctx Φ
\end{code}
Let `Γ` range over contexts.  In the last rule,
the type is indexed by the erasure of the previous
context to a type context and a kind.

The erasure of a context is a type context.
\begin{code}
--∥ ∅ ∥       =  ∅
--∥ Γ ,⋆ J ∥  =  ∥ Γ ∥ ,⋆ J
--∥ Γ , A ∥   =  ∥ Γ ∥
\end{code}

## Variables

A variable is indexed by its context and type.
\begin{code}
data _∋_ : ∀ {Φ J} (Γ : Ctx Φ) → Φ ⊢Nf⋆ J → Set where

  Z : ∀ {Φ Γ J} {A : Φ ⊢Nf⋆ J}
      ----------
    → Γ , A ∋ A

  S : ∀ {Φ Γ J K} {A : Φ ⊢Nf⋆ J} {B : Φ ⊢Nf⋆ K}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Φ Γ J K} {A : Φ ⊢Nf⋆ J}
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
open import Data.String

Tel : ∀ {Φ} Γ Δ → (∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J) → List (Δ ⊢Nf⋆ *) → Set

data _⊢_ : ∀ {Φ J} (Γ : Ctx Φ) → Φ ⊢Nf⋆ J → Set where

  ` : ∀ {Φ Γ J} {A : Φ ⊢Nf⋆ J}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}
    → String
    → Γ , A ⊢ B
      -----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ : ∀ {Φ Γ K}
    → (x : String)
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π x B

  _·⋆_ : ∀ {Φ Γ K x}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ⊢ Π x B
    → (A : Φ ⊢Nf⋆ K)
      ---------------
    → Γ ⊢ B [ A ]

  wrap1 : ∀{Φ Γ K}
   → (pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (arg : Φ ⊢Nf⋆ K)
   → (term : Γ ⊢ nf (embNf pat · (μ1 · embNf pat) · embNf arg))
   → Γ ⊢ ne (μ1 · pat · arg)

  unwrap1 : ∀{Φ Γ K}
    → {pat : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : Φ ⊢Nf⋆ K}
    → (term : Γ ⊢ ne (μ1 · pat · arg))
    → Γ ⊢ nf (embNf pat · (μ1 · embNf pat) · embNf arg)

  con : ∀{Φ}{Γ : Ctx Φ}{tcn}
    → TermCon {Φ} (con tcn)
      -------------------
    → Γ ⊢ con tcn

  builtin : ∀{Φ Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J)
    → Tel Γ Δ σ As
      ----------------------------------
    → Γ ⊢ substNf σ C

  error : ∀{Φ Γ} → (A : Φ ⊢Nf⋆ *) → Γ ⊢ A

Tel Γ Δ σ [] = ⊤
Tel Γ Δ σ (A ∷ As) = Γ ⊢ substNf σ A × Tel Γ Δ σ As

\end{code}

# Term Abbreviations
\begin{code}
--void : ∀{Γ} → Γ ⊢ unitNf
--void = Λ (ƛ (` Z))

true : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ booleanNf
true = Λ "α" (ƛ "t" (ƛ "f" (` (S Z))))

false : ∀{Φ}{Γ : Ctx Φ} → Γ ⊢ booleanNf
false = Λ "α" (ƛ "t" (ƛ "f" (` Z)))
\end{code}
