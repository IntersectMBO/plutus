\begin{code}
module TermIndexedByNormalType.Term where
\end{code}

## Imports

\begin{code}
open import Type
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.RenamingSubstitution renaming (_[_]Nf to _[_])

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
  _·E_ : ∀{J L} → EvalCxt Γ K (J ⇒ L) → Γ ⊢Nf⋆ J → EvalCxt Γ K L
\end{code}

\begin{code}
_[_]E : ∀{Γ K K'} → EvalCxt Γ K K' → Γ ⊢Nf⋆ K → Γ ⊢Nf⋆ K'
• [ t ]E = t
(E ·E u) [ t ]E = nf (embNf (E [ t ]E) · embNf u)
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
      ---------------
    → Γ ⊢ B [ A ]

  wrap : ∀{Γ K}
    → (S : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ K)
    → (E : EvalCxt ∥ Γ ∥ K K)
    → (M : Γ ⊢ E [ S [ ne (μ S) ] ]E)
    → {Q : ∥ Γ ∥ ⊢Nf⋆ K}
    → Q ≡ E [  ne (μ S) ]E
    → Γ ⊢ Q

  unwrap : ∀{Γ K}
    → {S : ∥ Γ ∥ ,⋆ K ⊢Nf⋆ K}
    → (E : EvalCxt ∥ Γ ∥ K K)
    → {Q : ∥ Γ ∥ ⊢Nf⋆ K}
    → Q ≡ E [ ne (μ S) ]E
    → (M : Γ ⊢ Q)
    → Γ ⊢ E [ S [ ne (μ S) ] ]E
\end{code}
