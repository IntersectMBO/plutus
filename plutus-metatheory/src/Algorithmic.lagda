\begin{code}
module Algorithmic where
\end{code}

## Imports

\begin{code}
open import Data.List using (List;[];replicate;_++_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl)
open import Data.List.NonEmpty using (length)

open import Utils hiding (TermCon)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z;S;Φ)
open _⊢⋆_

open import Type.BetaNormal using (_⊢Nf⋆_;_⊢Ne⋆_;weakenNf;renNf;embNf)
open _⊢Nf⋆_
open _⊢Ne⋆_

import Type.RenamingSubstitution as ⋆ using (Ren)
open import Type.BetaNBE using (nf)
open import Type.BetaNBE.RenamingSubstitution using (subNf;SubNf) renaming (_[_]Nf to _[_])

open import Builtin using (Builtin;signature)
open Builtin.Builtin
open import Builtin.Signature using (Sig;sig;nat2Ctx⋆;fin2∈⋆)

open import Builtin.Constant.Term Ctx⋆ Kind * _⊢Nf⋆_ con using (TermCon)
open import Builtin.Constant.Type Ctx⋆ (_⊢Nf⋆ *) using (TyCon)
open TyCon

open Builtin.Signature.FromSig Ctx⋆ (_⊢Nf⋆ *) nat2Ctx⋆ (λ x → ne (` (fin2∈⋆ x))) con _⇒_ Π using (sig2type)
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
  _,⋆_ : Ctx Φ → (J : Kind) → Ctx (Φ ,⋆ J)
  _,_  : (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → Ctx Φ
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
data _∋_ : (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → Set where

  Z : ∀ {Γ} {A : Φ ⊢Nf⋆ *}
      ----------
    → Γ , A ∋ A

  S : ∀ {Γ} {A : Φ ⊢Nf⋆ *} {B : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : ∀ {Γ K}{A : Φ ⊢Nf⋆ *}
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
btype : Builtin → Φ ⊢Nf⋆ *
btype b = subNf (λ()) (sig2type (signature b))

postulate btype-ren : ∀{Φ Ψ} b (ρ : ⋆.Ren Φ Ψ) → btype b ≡ renNf ρ (btype b)
postulate btype-sub : ∀{Φ Ψ} b (ρ : SubNf Φ Ψ) → btype b ≡ subNf ρ (btype b)

infixl 7 _·⋆_/_

data _⊢_ (Γ : Ctx Φ) : Φ ⊢Nf⋆ * → Set where

  ` : ∀ {A : Φ ⊢Nf⋆ *}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ : ∀ {A B : Φ ⊢Nf⋆ *}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _·_ : ∀ {A B : Φ ⊢Nf⋆ *}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  Λ : ∀ {K}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ,⋆ K ⊢ B
      -------------------
    → Γ ⊢ Π B

  _·⋆_/_ : ∀ {K C}
    → {B : Φ ,⋆ K ⊢Nf⋆ *}
    → Γ ⊢ Π B
    → (A : Φ ⊢Nf⋆ K)
    → C ≡ B [ A ]
      --------------
    → Γ ⊢ C

  wrap : ∀{K}
   → (A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *)
   → (B : Φ ⊢Nf⋆ K)
   → Γ ⊢ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)
     -------------------------------------------------------------
   → Γ ⊢ μ A B

  unwrap : ∀{K C}
    → {A : Φ ⊢Nf⋆ (K ⇒ *) ⇒ K ⇒ *}
    → {B : Φ ⊢Nf⋆ K}
    → Γ ⊢ μ A B
    → C ≡ nf (embNf A · ƛ (μ (embNf (weakenNf A)) (` Z)) · embNf B)
      -------------------------------------------------------------
    → Γ ⊢ C

  con : ∀{tcn}
    → TermCon {Φ} (con tcn)
      ---------------------
    → Γ ⊢ con tcn

  builtin_/_ : ∀{C}
    → (b :  Builtin)
    → C ≡ btype b
      --------------
    → Γ ⊢ C

  error :
      (A : Φ ⊢Nf⋆ *)
      --------------
    → Γ ⊢ A
\end{code}

Utility functions

\begin{code}
conv∋ : ∀ {Γ Γ'}{A A' : Φ ⊢Nf⋆ *}
 → Γ ≡ Γ'
 → A ≡ A'
 → Γ ∋ A
 → Γ' ∋ A'
conv∋ refl refl x = x

conv⊢ : ∀ {Γ Γ'}{A A' : Φ ⊢Nf⋆ *}
 → Γ ≡ Γ'
 → A ≡ A'
 → Γ ⊢ A
 → Γ' ⊢ A'
conv⊢ refl refl t = t

Ctx2type : (Γ : Ctx Φ) → Φ ⊢Nf⋆ * → ∅ ⊢Nf⋆ *
Ctx2type ∅        C = C
Ctx2type (Γ ,⋆ J) C = Ctx2type Γ (Π C)
Ctx2type (Γ , x)  C = Ctx2type Γ (x ⇒ C)

data Arg : Set where
  Term Type : Arg

Arity = List Arg

arity : Builtin → Arity
arity b with signature b 
... | sig n ar _ = replicate n Type ++ replicate (length ar) Term

\end{code}
  
When signatures supported universal quantifiers to be interleaved with other 
parameters it made sense for `Arity` to be defined as above. Now that we don't,
`Arity` should be rewritten to be two numbers (`n` and `length ar` above), representing
the number of quantifiers and the number of (term) parameters.
We keep `Arity` this way in order to make the current implementation works, 
but it will be changed.