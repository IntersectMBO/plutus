---
title: Declarative syntax
layout: page
---

```
module Declarative where
```

## Imports

```
open import Relation.Binary.PropositionalEquality using (_≡_;refl)

open import Type using (Ctx⋆;_⊢⋆_;_∋⋆_;Φ;Ψ;A;B)
open Ctx⋆
open _⊢⋆_
open _∋⋆_

open import Type.RenamingSubstitution using (weaken;sub;Ren;ren;Sub;_[_])
open import Type.Equality using (_≡β_)
open import Builtin using (Builtin;signature)
open Builtin.Builtin

open import Builtin.Signature using (nat2Ctx⋆;fin2∈⋆)

open import Utils using (Kind;*;_⇒_;K)
open import Builtin.Constant.Type using (TyCon)
open TyCon

open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con using (TermCon)

open Builtin.Signature.FromSig Ctx⋆ (_⊢⋆ *) nat2Ctx⋆ (λ x → ` (fin2∈⋆ x)) con _⇒_ Π using (sig2type)
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

Compute the type for a builtin:

```
btype : Builtin → Φ ⊢⋆ *
btype b = sub (λ()) (sig2type (signature b))
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

  builtin : (b : Builtin)
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
