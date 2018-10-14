\begin{code}
module TermIndexedBySyntacticType.Term where
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution
open import Type.Equality

open import Relation.Binary.PropositionalEquality hiding ([_])
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.
\begin{code}
infix  4 _∋_
infix  4 _⊢_
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
• [ t ]E = t
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

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.
\begin{code}
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

  conv : ∀{Γ J}
    → {A B : ∥ Γ ∥ ⊢⋆ J}
    → A ≡β B
    → Γ ⊢ A
      -----
    → Γ ⊢ B
\end{code}
