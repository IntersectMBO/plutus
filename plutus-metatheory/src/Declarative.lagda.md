---
title: Declarative syntax
layout: page
---

```
module Declarative where
```

## Imports

```
open import Type
open import Type.RenamingSubstitution
open import Type.Equality
open import Builtin
open import Utils hiding (TermCon)
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con

open import Relation.Binary.PropositionalEquality
  hiding ([_]) renaming (subst to substEq)
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
open import Data.Sum
open import Function hiding (_∋_;typeOf)
import Data.Bool as Bool
open import Data.String
```

## Fixity declarations

To begin, we get all our infix declarations out of the way.
We list separately operators for judgements, types, and terms.

```
infix  4 _∋_
infix  3 _⊢_
infixl 5 _,_
```

## Contexts and erasure

A context is either empty, or extends a context by a type variable of
a given kind, or extends a context by a variable of a given
type.

Contexts are indexed by type contexts. The type context has all the
same type variables as the term context but no term variables.

```
data Ctx : Ctx⋆ → Set where
  ∅ : Ctx ∅
  _,⋆_ : Ctx Φ → (J : Kind) → Ctx (Φ ,⋆ J)
  _,_ : (Γ : Ctx Φ) → Φ ⊢⋆ * → Ctx Φ
```

Let `Γ`, `Δ` range over contexts:
```
variable
  Γ Δ : Ctx Φ
```

## Variables

A variable is indexed by its context and type. Notice there is only
one Z as a type variable cannot be a term.

```
data _∋_ : (Γ : Ctx Φ) → Φ ⊢⋆ * → Set where
  Z : ----------
      Γ , A ∋ A

  S : Γ ∋ A
      ----------
    → Γ , B ∋ A

  T : Γ ∋ A
      -------------------
    → Γ ,⋆ K ∋ weaken A
```

Let `x`, `y` range over variables.

## Builtin Machinery

Computing a signature for a builtin. Ideally this should be done generically:
```
sig : Builtin → Σ Ctx⋆ λ Φ → Ctx Φ × Φ ⊢⋆ *
sig ifThenElse = ∅ ,⋆ * ,, ∅ ,⋆ * , con bool , ` Z , ` Z ,, ` Z
sig addInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
sig subtractInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
sig multiplyInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
sig divideInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
sig quotientInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
sig remainderInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
sig modInteger = ∅ ,, ∅ , con integer , con integer ,, con integer
sig lessThanInteger = ∅ ,, ∅ , con integer , con integer ,, con bool
sig lessThanEqualsInteger = ∅ ,, ∅ , con integer , con integer ,, con bool
sig equalsInteger = ∅ ,, ∅ , con integer , con integer ,, con bool
sig appendByteString = ∅ ,, ∅ , con bytestring , con bytestring ,, con bytestring
sig lessThanByteString = ∅ ,, ∅ , con bytestring , con bytestring ,, con bool
sig lessThanEqualsByteString =
  ∅ ,, ∅ , con bytestring , con bytestring ,, con bool
sig sha2-256 = ∅ ,, ∅ , con bytestring ,, con bytestring
sig sha3-256 = ∅ ,, ∅ , con bytestring ,, con bytestring
sig verifySignature = ∅ ,, ∅ , con bytestring , con bytestring , con bytestring ,, con bool
sig equalsByteString = ∅ ,, ∅ , con bytestring , con bytestring ,, con bool 
sig appendString = ∅ ,, ∅ , con string , con string ,, con string
sig trace = ∅ ,, ∅ , con string ,, con unit
sig _ = ∅ ,, ∅ ,, con unit -- TODO: add support for remaining builtins
```

Converting a signature to a totally unsaturated type:

```
isig2type : (Φ : Ctx⋆) → Ctx Φ → Φ ⊢⋆ * → ∅ ⊢⋆ *
isig2type .∅ ∅ C = C
isig2type (Φ ,⋆ J) (Γ ,⋆ J) C = isig2type Φ Γ (Π C)
isig2type Φ        (Γ ,  A) C = isig2type Φ Γ (A ⇒ C)
```

Compute the type for a builtin:

```
btype : Builtin → Φ ⊢⋆ *
btype b = let Φ ,, Γ ,, C = sig b in sub (λ()) (isig2type Φ Γ C)
```

Two lemmas concerning renaming and substituting types of builtins:

```
postulate btype-ren : ∀ b (ρ : Ren Φ Ψ) → btype b ≡ ren ρ (btype b)
postulate btype-sub : ∀ b (ρ : Sub Φ Ψ) → btype b ≡ sub ρ (btype b)
```

## Terms

A term is indexed over by its context and type.  A term is a variable,
an abstraction, an application, a type abstraction, or a type
application.


```
data _⊢_ (Γ : Ctx Φ) : Φ ⊢⋆ * → Set where

  ` : Γ ∋ A
      ------
    → Γ ⊢ A

  ƛ : Γ , A ⊢ B
      ----------
    → Γ ⊢ A ⇒ B

  _·_ : Γ ⊢ A ⇒ B
      → Γ ⊢ A
        ----------
      → Γ ⊢ B

  Λ : Γ ,⋆ K ⊢ B
      ----------
    → Γ ⊢ Π B

  _·⋆_ : Γ ⊢ Π B
       → (A : Φ ⊢⋆ K)
         ------------
       → Γ ⊢ B [ A ]

  wrap : (A : Φ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *)
       → (B : Φ ⊢⋆ K)
       → Γ ⊢ A · ƛ (μ (weaken A) (` Z)) · B
         ----------------------------------
       → Γ ⊢ μ A B

  unwrap : Γ ⊢ μ A B
           ----------------------------------
         → Γ ⊢ A · ƛ (μ (weaken A) (` Z)) · B

  conv : A ≡β B
       → Γ ⊢ A
         -----
       → Γ ⊢ B

  con : ∀ {c}
      →  TermCon {Φ} (con c)
        ---------------
      → Γ ⊢ con c

  builtin : (b :  Builtin)
            --------------
          → Γ ⊢ btype b

  error : (A : Φ ⊢⋆ *)
          ------------
        → Γ ⊢ A
```

Substituting types or contexts of term variables by propositionally
equal ones:

```
conv∋ : Γ ≡ Δ
      → A ≡ B
      → Γ ∋ A
      → Δ ∋ B
conv∋ refl refl t = t
```

Substituting types or contexts of terms by propositionally equal ones:

```
conv⊢ : Γ ≡ Δ
      → A ≡ B
      → Γ ⊢ A
      → Δ ⊢ B
conv⊢ refl refl t = t
```

getting the type of a term, a var, and the pieces of πs and μs

```
typeOf : ∀{Γ : Ctx Φ} → Γ ⊢ A → Φ ⊢⋆ *
typeOf {A = A} _ = A

typeOf∋ : ∀{Γ : Ctx Φ} → Γ ∋ A → Φ ⊢⋆ *
typeOf∋ {A = A} _ = A

piBody : {A : Φ ,⋆ K ⊢⋆ *} → Γ ⊢ Π A → Φ ,⋆ K ⊢⋆ *
piBody {A = A} _ = A

muPat : {A : Φ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *} → Γ ⊢ μ A B → Φ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *
muPat {A = A} _ = A

muArg : {B : Φ ⊢⋆ K} → Γ ⊢ μ A B → Φ ⊢⋆ K
muArg {B = B} _ = B
```
