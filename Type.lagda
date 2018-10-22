\begin{code}
module Type where
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.

\begin{code}
infix  4 _∋⋆_
infix  4 _⊢⋆_
infixl 5 _,⋆_

infix  6 Π
infixr 7 _⇒_

infix  5 ƛ
infixl 7 _·_
infix  9 S
\end{code}

## Kinds

The kind of types is `*`. Plutus core core is based on System Fω which
is higher order so we have `⇒` for type level functions. We also have
a kind called `size`. There are no terms of kind `size`, instead
`size` apears in types to support sized integers, etc.

\begin{code}
data Kind : Set where
  * : Kind
  size : Kind
  _⇒_ : Kind → Kind → Kind
\end{code}

Let `J`, `K` range over kinds.

## Type contexts

A type context is either empty or extends a type
context by a type variable of a given kind.

\begin{code}
data Ctx⋆ : Set where
  ∅ : Ctx⋆
  _,⋆_ : Ctx⋆ → Kind → Ctx⋆
\end{code}

Let `Φ`, `Ψ` range over type contexts.

## Type variables

A type variable is indexed by its context and kind.

\begin{code}
data _∋⋆_ : Ctx⋆ → Kind → Set where

  Z : ∀ {Φ J}
      -------------
    → Φ ,⋆ J ∋⋆ J

  S : ∀ {Φ J K}
    → Φ ∋⋆ J
      -------------
    → Φ ,⋆ K ∋⋆ J
\end{code}

Let `α`, `β` range over type variables.

## Types

A type is indexed by its context and kind.  A type is either a type
variable, a pi type, or a function type.

\begin{code}
data _⊢⋆_ : Ctx⋆ → Kind → Set where

  ` : ∀ {Φ J}
    → Φ ∋⋆ J
      --------
    → Φ ⊢⋆ J

  Π : ∀ {Φ K}
    → Φ ,⋆ K ⊢⋆ *
      -----------
    → Φ ⊢⋆ *

  _⇒_ : ∀ {Φ}
    → Φ ⊢⋆ *
    → Φ ⊢⋆ *
      ------
    → Φ ⊢⋆ *

  ƛ :  ∀ {Φ K J}
    → Φ ,⋆ K ⊢⋆ J 
      -----------
    → Φ ⊢⋆ K ⇒ J

  _·_ : ∀{Φ K J}
    → Φ ⊢⋆ K ⇒ J
    → Φ ⊢⋆ K
      ------
    → Φ ⊢⋆ J

  μ : ∀{φ K}
    → φ ,⋆ K ⊢⋆ K
      -----------
    → φ ⊢⋆ K

\end{code}
