\begin{code}
module Declarative.Term where
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution
open import Type.Equality
open import Builtin
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * # _∋⋆_ Z S _⊢⋆_ ` con boolean size⋆
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢⋆_ con size⋆

open import Relation.Binary.PropositionalEquality hiding ([_]; subst)
open import Agda.Builtin.Int
open import Data.Integer renaming (_*_ to _**_)
open import Data.Empty
open import Data.Product hiding (_,_)
open import Relation.Binary hiding (_⇒_)
import Data.Nat as ℕ
open import Data.Unit hiding (_≤_)
open import Data.Vec hiding ([_]; take; drop)
open import Data.List hiding ([_]; length; take; drop)
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat hiding (_^_; _≤_; _<_; _>_; _≥_)
open import Function hiding (_∋_)
import Data.Bool as Bool
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _∋_
infix  3 _⊢_
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
  _,_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢⋆ J → Ctx
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
data _∋_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢⋆ J → Set where

  Z : ∀ {Γ J} {A : ∥ Γ ∥ ⊢⋆ J}
      ----------
    → Γ , A ∋ A

  S : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢⋆ J} {B : ∥ Γ ∥ ⊢⋆ K}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢⋆ J}
    → Γ ∋ A
      -------------------
    → Γ ,⋆ K ∋ weaken A
\end{code}
Let `x`, `y` range over variables.

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.

\begin{code}
Tel : ∀ Γ Δ → Sub Δ ∥ Γ ∥ → List (Δ ⊢⋆ *) → Set

data _⊢_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢⋆ J → Set where

  ` : ∀ {Γ J} {A : ∥ Γ ∥ ⊢⋆ J}
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

  Λ : ∀ {Γ K} {B : ∥ Γ ∥ ,⋆ K ⊢⋆ *}
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π B

  _·⋆_ : ∀ {Γ K B}
    → Γ ⊢ Π  B
    → (A : ∥ Γ ∥ ⊢⋆ K)
      ---------------
    → Γ ⊢ B [ A ]

  wrap1 : ∀{Γ K}
   → (pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (arg : ∥ Γ ∥ ⊢⋆ K)
   → (term : Γ ⊢ pat · (μ1 · pat) · arg)
   → Γ ⊢ μ1 · pat · arg

  unwrap1 : ∀{Γ K}
    → {pat : ∥ Γ ∥ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {arg : ∥ Γ ∥ ⊢⋆ K}
    → (term : Γ ⊢ μ1 · pat · arg)
    → Γ ⊢ pat · (μ1 · pat) · arg
    
  conv : ∀{Γ J}
    → {A B : ∥ Γ ∥ ⊢⋆ J}
    → A ≡β B
    → Γ ⊢ A
      -----
    → Γ ⊢ B

  con : ∀{Γ s tcn}
    → TermCon (con tcn s)
      -------------------
    → Γ ⊢ con tcn s

  builtin : ∀{Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : Sub Δ ∥ Γ ∥) -- substitutes for new vars introduced by the Sig
    → Tel Γ Δ σ As     -- a telescope of terms M_i typed in subst σ
    -----------------------------
    → Γ ⊢ subst σ C

  error : ∀{Γ} → (A : ∥ Γ ∥ ⊢⋆ *) → Γ ⊢ A

Tel Γ Δ σ [] = ⊤
Tel Γ Δ σ (A ∷ As) = Γ ⊢ subst σ A × Tel Γ Δ σ As
\end{code}

# Term Abbreviations
\begin{code}
void : ∀{Γ} → Γ ⊢ unit
void = Λ (ƛ (` Z))

true : ∀{Γ} → Γ ⊢ boolean
true = Λ (ƛ (ƛ (` (S Z))))

false : ∀{Γ} → Γ ⊢ boolean
false = Λ (ƛ (ƛ (` Z)))
\end{code}
