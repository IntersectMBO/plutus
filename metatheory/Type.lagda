\begin{code}
module Type where
\end{code}

## Fixity declarations

To begin, we get all our infix declarations out of the way.

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

## Imports

\begin{code}
open import Agda.Builtin.Nat

open import Builtin.Constant.Type
\end{code}

## Kinds

The kind of types is `*`. Plutus core core is based on System Fω which
is higher order so we have `⇒` for type level functions. We also have
a kind called `#` which is used for sized integers and bytestrings.

\begin{code}
data Kind : Set where
  *   : Kind               -- type
  _⇒_ : Kind → Kind → Kind -- function kind

{-# FOREIGN GHC import Scoped #-}
{-# COMPILE GHC Kind = data ScKind (ScKiStar | ScKiFun) #-}

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

Type variables are not named, they are numbered (de Bruijn indices).

A type variable is indexed by its context and kind. For a given
context, it's impossible to construct a variable that is out of
scope.

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

A type is indexed by its context and kind. Types are intrinsically
scoped and kinded: it's impossible to construct an ill-kinded
application and it's impossible to refer to a variable that is not in
scope.

A type is either a type variable, a pi type, a function type, a
lambda, an application, an iso-recursive type `μ`, a size, or a type
constant (base type). Note that recursive types range over an
arbitrary kind `k` which goes beyond standard iso-recursive types.

\begin{code}
open import Data.String

data _⊢⋆_ : Ctx⋆ → Kind → Set where

  ` : ∀ {Φ J}
    → Φ ∋⋆ J
      --------
    → Φ ⊢⋆ J

  Π : ∀ {Φ K}
    → String
    → Φ ,⋆ K ⊢⋆ *
      -----------
    → Φ ⊢⋆ *

  _⇒_ : ∀ {Φ}
    → Φ ⊢⋆ *
    → Φ ⊢⋆ *
      ------
    → Φ ⊢⋆ *

  ƛ :  ∀ {Φ K J}
    → String
    → Φ ,⋆ K ⊢⋆ J 
      -----------
    → Φ ⊢⋆ K ⇒ J

  _·_ : ∀{Φ K J}
    → Φ ⊢⋆ K ⇒ J
    → Φ ⊢⋆ K
      ------
    → Φ ⊢⋆ J

  μ1 : ∀{φ K}
      --------------------------------
    → φ ⊢⋆ ((K ⇒ *) ⇒ K ⇒ *) ⇒ K ⇒ *

  con : ∀{φ}
    → TyCon
      ------
    → φ ⊢⋆ *

\end{code}

Let `A`, `B`, `C` range over types.

## Type Abbreviations
TODO: these should be in the stdlib
\begin{code}
unit : ∀{Γ} → Γ ⊢⋆ *
unit = Π "α" (` Z ⇒ ` Z)

boolean : ∀{Γ} → Γ ⊢⋆ *
boolean = Π "α" (` Z ⇒ ` Z ⇒ ` Z)
\end{code}

\begin{code}
open import Relation.Binary.PropositionalEquality

data _≡α_ {Γ} : ∀{J} → Γ ⊢⋆ J → Γ ⊢⋆ J → Set where
  var≡α : ∀{J}{α α' : Γ ∋⋆ J} → α ≡ α' → ` α ≡α ` α'

  ⇒≡α : {A A' B B' : Γ ⊢⋆ *}
    → A ≡α A'
    → B ≡α B'
      ---------------------
    → (A ⇒ B) ≡α (A' ⇒ B')
    
  Π≡α : ∀{J}{B B' : Γ ,⋆ J ⊢⋆ *}{x}{x'}
    → B ≡α B'
      -------
    → Π x B ≡α Π x' B'
    
  ƛ≡α : ∀{K J}{B B' : Γ ,⋆ J ⊢⋆ K}{x}{x'}
    → B ≡α B'
      ---------------
    → ƛ x B ≡α ƛ x' B'
    
  ·≡α : ∀{K J}{A A' : Γ ⊢⋆ K ⇒ J}{B B' : Γ ⊢⋆ K}
    → A ≡α A'
    → B ≡α B'
      --------------------
    → (A · B) ≡α (A' · B')

  μ≡α : ∀{K} →  μ1 {K = K} ≡α μ1

  con≡α : ∀ {c} → con c ≡α con c

reflα : ∀{Φ J}{A : Φ ⊢⋆ J} → A ≡α A
reflα {A = ` α}   = var≡α refl
reflα {A = Π x A} = Π≡α reflα
reflα {A = A ⇒ B} = ⇒≡α reflα reflα
reflα {A = ƛ x A} = ƛ≡α reflα
reflα {A = A · B} = ·≡α reflα reflα
reflα {A = μ1}    = μ≡α
reflα {A = con c} = con≡α


symα : ∀{Φ J}{A A' : Φ ⊢⋆ J} → A ≡α A' → A' ≡α A
symα (var≡α p) = var≡α (sym p)
symα (⇒≡α p q) = ⇒≡α (symα p) (symα q)
symα (Π≡α p)   = Π≡α (symα p)
symα (ƛ≡α p)   = ƛ≡α (symα p)
symα (·≡α p q) = ·≡α (symα p) (symα q)
symα μ≡α       = μ≡α
symα con≡α     = con≡α

transα : ∀{Φ J}{A A' A'' : Φ ⊢⋆ J} → A ≡α A' → A' ≡α A'' → A ≡α A''
transα (var≡α p) (var≡α p')  = var≡α (trans p p')
transα (⇒≡α p q) (⇒≡α p' q') = ⇒≡α (transα p p') (transα q q')
transα (Π≡α p)   (Π≡α p')    = Π≡α (transα p p')
transα (ƛ≡α p)   (ƛ≡α p')    = ƛ≡α (transα p p')
transα (·≡α p q) (·≡α p' q') = ·≡α (transα p p') (transα q q')
transα μ≡α       μ≡α         = μ≡α
transα con≡α     con≡α       = con≡α
\end{code}
