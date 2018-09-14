\begin{code}
module Term where
\end{code}

## Imports

\begin{code}
open import Type
open import Type.RenamingSubstitution
open import Type.Normal
open import Type.Value
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
  _,_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢V⋆ J → Ctx
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
data _∋_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢V⋆ J → Set where

  Z : ∀ {Γ J} {A : ∥ Γ ∥ ⊢V⋆ J}
      ----------
    → Γ , A ∋ A

  S_ : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢V⋆ J} {B : ∥ Γ ∥ ⊢V⋆ K}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T_ : ∀ {Γ J K} {A : ∥ Γ ∥ ⊢V⋆ J}
    → Γ ∋ A
      -------------------
    → Γ ,⋆ K ∋ weakenV A
\end{code}
Let `x`, `y` range over variables.

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.
\begin{code}
data _⊢_ : ∀ {J} (Γ : Ctx) → ∥ Γ ∥ ⊢V⋆ J → Set where

  `_ : ∀ {Γ J} {A : ∥ Γ ∥ ⊢V⋆ J}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ_ : ∀ {Γ A B}
    → Γ , A ⊢ B
      -----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ_ : ∀ {Γ K}
    → {B : ∥ Γ ∥ ,⋆ K ⊢⋆ *}
    → Γ ,⋆ K ⊢ eval B idEnv
      ----------
    → Γ ⊢ Π B idEnv

  _·⋆_ : ∀ {Γ K}
    → {B : ∥ Γ ∥ ,⋆ K ⊢⋆ *}
    → Γ ⊢ Π B idEnv
    → (A : ∥ Γ ∥ ⊢V⋆ K)
      ---------------
    → Γ ⊢ B ⟦ A ⟧

  wrap : ∀{Γ}
    → {B : ∥ Γ ∥ ,⋆ * ⊢⋆ *}
    → (M : Γ ⊢ B ⟦ μ B idEnv ⟧)
    → Γ ⊢ μ B idEnv

  unwrap : ∀{Γ}
    → {B : ∥ Γ ∥ ,⋆ * ⊢⋆ *}
    → (M : Γ ⊢ μ B idEnv)
    → Γ ⊢ B ⟦ μ B idEnv ⟧

  conv : ∀{Γ}{A A' : ∥ Γ ∥ ⊢V⋆ *}
    → A V≡ A'
    → Γ ⊢ A
    → Γ ⊢ A'
\end{code}
