\begin{code}
module Algorithmic where
\end{code}

## Imports

\begin{code}
open import Function hiding (_∋_)
open import Data.Product renaming (_,_ to _,,_)
open import Data.List hiding ([_])
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit

open import Type
open import Type.BetaNormal
open import Type.BetaNBE
open import Type.BetaNBE.RenamingSubstitution renaming (_[_]Nf to _[_])
open import Builtin
open import Builtin.Signature
  Ctx⋆ Kind ∅ _,⋆_ * _∋⋆_ Z S _⊢Nf⋆_ (ne ∘ `) con
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con
open import Builtin.Constant.Type
open import Utils
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
  _,_  : ∀ {Φ} (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → Ctx Φ
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
open import Type.BetaNormal.Equality
data _∋_ : ∀ {Φ} (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → Set where

  Z : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *}
      ----------
    → Γ , A ∋ A

  S : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *} {B : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Φ Γ K}{A : Φ ⊢Nf⋆ *}
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

data Tel {Φ} Γ Δ (σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J) : List (Δ ⊢Nf⋆ *) → Set

data _⊢_ : ∀ {Φ} (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → Set where

  ` : ∀ {Φ Γ} {A : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}
    → Γ , A ⊢ B
      -----------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {Φ Γ}{A B : Φ ⊢Nf⋆ *}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      -----------
    → Γ ⊢ B

  Λ : ∀ {Φ Γ K}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π B

  _·⋆_ : ∀ {Φ Γ K}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ⊢ Π B
    → (A : Φ ⊢Nf⋆ K)
      ---------------
    → Γ ⊢ B [ A ]

  wrap : ∀{Φ Γ K}
   → (A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (B : Φ ⊢Nf⋆ K)
   → Γ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)
   → Γ ⊢ μ A B

  unwrap : ∀{Φ Γ K}
    → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : Φ ⊢Nf⋆ K}
    → Γ ⊢ μ A B
    → Γ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)

  con : ∀{Φ}{Γ : Ctx Φ}{tcn}
    → TermCon {Φ} (con tcn)
      -------------------
    → Γ ⊢ con tcn

  builtin : ∀{Φ Γ}
    → (bn : Builtin)
    → let Δ ,, As ,, C = SIG bn in
      (σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J)
    → Tel Γ Δ σ As
      -------------------------------
    → Γ ⊢ substNf σ C

  error : ∀{Φ Γ} → (A : Φ ⊢Nf⋆ *) → Γ ⊢ A

data Tel {Φ} Γ Δ σ where
  []  : Tel Γ Δ σ []
  _∷_ : ∀{A As} → Γ ⊢ substNf σ A → Tel Γ Δ σ As →  Tel Γ Δ σ (A ∷ As)
\end{code}

Utility functions

\begin{code}
_++T_ : ∀ {Φ Γ Δ}{σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J}
  → {As : List (Δ ⊢Nf⋆ *)}
  → {As' : List (Δ ⊢Nf⋆ *)}
  → (ts  : Tel Γ Δ σ As)
  → (ts' : Tel Γ Δ σ As')
  → Tel Γ Δ σ (As Data.List.++ As')
[]       ++T ts' = ts'
(t ∷ ts) ++T ts' = t ∷ (ts ++T ts')


_:<T_ : ∀ {Φ Γ Δ}{σ : ∀ {J} → Δ ∋⋆ J → Φ ⊢Nf⋆ J}
  → {As : List (Δ ⊢Nf⋆ *)}
  → {A  : Δ ⊢Nf⋆ *}
  → (ts : Tel Γ Δ σ As)
  → (t : Γ ⊢ substNf σ A)
  → Tel Γ Δ σ (As :<L A)
[]        :<T t = t ∷ []
(t' ∷ ts) :<T t = t' ∷ (ts :<T t)

open import Type.BetaNormal.Equality

conv∋ : ∀ {Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}
 → Γ ≡ Γ'
 → A ≡ A'
 → Γ ∋ A
 → Γ' ∋ A'
conv∋ refl refl x = x

open import Type.BetaNBE.Completeness
open import Type.Equality
open import Type.BetaNBE.RenamingSubstitution

conv⊢ : ∀ {Φ Γ Γ'}{A A' : Φ ⊢Nf⋆ *}
 → Γ ≡ Γ'
 → A ≡ A'
 → Γ ⊢ A
 → Γ' ⊢ A'
conv⊢ refl refl t = t

convTel : ∀ {Φ Ψ}{Γ Γ' : Ctx Φ}
  → Γ ≡ Γ'
  → (σ : ∀{J} → Ψ ∋⋆ J → Φ ⊢Nf⋆ J)
  → (As : List (Ψ ⊢Nf⋆ *))
  → Tel Γ Ψ σ As → Tel Γ' Ψ σ As
convTel p σ []       []       = []
convTel p σ (A ∷ As) (t ∷ ts) = conv⊢ p refl t ∷ convTel p σ As ts
\end{code}
