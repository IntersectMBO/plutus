\begin{code}
module TermIndexedBySyntacticType.Term where
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution
open import Type.Equality

open import Relation.Binary.PropositionalEquality hiding ([_]; subst)
open import Agda.Builtin.Int
open import Data.Empty
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _∋_
infix  3 _⊢_
infixl 5 _,_
\end{code}

# Evaluation contexts
the first index is the kind of the hole, the second index is the type of the evalcxt
\begin{code}
data EvalCxt Γ (K : Kind) : Kind → Set where
  •    : EvalCxt Γ K K
  _·E_ : ∀{J L} → EvalCxt Γ K (J ⇒ L) → Γ ⊢⋆ J → EvalCxt Γ K L
\end{code}

\begin{code}
_[_]E : ∀{Γ K K'} → EvalCxt Γ K K' → Γ ⊢⋆ K → Γ ⊢⋆ K'
•        [ t ]E = t
(E ·E u) [ t ]E = E [ t ]E · u
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

## Term Constants

\begin{code}
data TermCon {Φ} : Φ ⊢⋆ * → Set where
  integer    : ∀ s → Int → TermCon (con integer s)
  bytestring : ∀ s → ⊥   → TermCon (con integer s)
  size       : ∀ s       → TermCon (con size s) 
\end{code}

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.
\begin{code}
open import Data.Vec hiding ([_])
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to _,,_)
open import Data.Nat
open import Function hiding (_∋_)

Sig : Ctx → Ctx → Set
Sig Δ Γ = List (∥ Δ ∥ ⊢⋆ *) × ∥ Δ ∥ ⊢⋆ *


data Builtin  : Set where
  addInteger       : Builtin
  substractInteger : Builtin

El : Builtin → ∀ Γ → Σ Ctx λ Δ → Sig Δ Γ
-- could have just one context so Signatures extend from ∅...
El addInteger       Γ =
  (Γ ,⋆ #) ,, (con integer (` Z) ∷ con integer (` Z) ∷ []) ,, con integer (` Z)
El substractInteger Γ = 
  (Γ ,⋆ #) ,, (con integer (` Z) ∷ con integer (` Z) ∷ []) ,, con integer (` Z)

Tel : ∀ Γ Δ → Sub ∥ Δ ∥ ∥ Γ ∥ → List (∥ Δ ∥ ⊢⋆ *) → Set

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

  _·⋆_ : ∀ {Γ B}
    → Γ ⊢ Π B
    → (A : ∥ Γ ∥ ⊢⋆ *)
      ---------------
    → Γ ⊢ B [ A ]

  wrap : ∀{Γ K}
    → (S : ∥ Γ ∥ ,⋆ K ⊢⋆ K)
    → (E : EvalCxt ∥ Γ ∥ K K)
    → (M : Γ ⊢ E [ S [ μ S ] ]E)
    → {Q : ∥ Γ ∥ ⊢⋆ K}
    → Q ≡ E [ μ S ]E
    → Γ ⊢ Q

  unwrap : ∀{Γ K}
    → {S : ∥ Γ ∥ ,⋆ K ⊢⋆ K}
    → (E : EvalCxt ∥ Γ ∥ K K)
    → {Q : ∥ Γ ∥ ⊢⋆ K}
    → Q ≡ E [ μ S ]E
    → (M : Γ ⊢ Q)
    → Γ ⊢ E [ S [ μ S ] ]E

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
    → let Δ ,, As ,, C = El bn Γ in
      (σ : Sub ∥ Δ ∥ ∥ Γ ∥) -- substitutes for new vars introduced by the Sig
    → Tel Γ Δ σ As         -- a telescope of terms M_i typed in subst σ A_i
      -----------------------------
    → Γ ⊢ subst σ C

open import Data.Unit
Tel Γ Δ σ [] = ⊤
Tel Γ Δ σ (A ∷ As) = Γ ⊢ subst σ A × Tel Γ Δ σ As

\end{code}
