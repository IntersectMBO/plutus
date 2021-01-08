---
title: Types
layout: page
---

```
module Type where
```

## Fixity declarations

To begin, we get all our infix declarations out of the way.

```
infix  4 _∋⋆_
infix  4 _⊢⋆_
infixl 5 _,⋆_

infix  6 Π
infixr 7 _⇒_
infix  5 ƛ
infixl 7 _·_
infix  9 S
```

## Imports

```
open import Agda.Builtin.Nat
open import Builtin.Constant.Type
```

## Kinds

The kind of types is `*`. Plutus core core is based on System Fω which
is higher order so we have `⇒` for type level functions. We also have
a kind called `#` which is used for sized integers and bytestrings.

```
data Kind : Set where
  *   : Kind               -- type
  _⇒_ : Kind → Kind → Kind -- function kind

{-# FOREIGN GHC import Scoped #-}
{-# COMPILE GHC Kind = data ScKind (ScKiStar | ScKiFun) #-}
```

Let `J`, `K` range over kinds:
```
variable
  J K : Kind
```

## Type contexts

A type context is either empty or extends a type
context by a type variable of a given kind.

```
data Ctx⋆ : Set where
  ∅ : Ctx⋆
  _,⋆_ : Ctx⋆ → Kind → Ctx⋆
```

Let `Φ`, `Ψ`, `Θ` range over type contexts:
```
variable
  Φ Ψ Θ : Ctx⋆
```

## Type variables

Type variables are not named, they are numbered (de Bruijn indices).

A type variable is indexed by its context and kind. For a given
context, it's impossible to construct a variable that is out of
scope.

```
data _∋⋆_ : Ctx⋆ → Kind → Set where

  Z : -------------
      Φ ,⋆ J ∋⋆ J

  S : Φ ∋⋆ J
      -------------
    → Φ ,⋆ K ∋⋆ J
```

Let `α`, `β` range over type variables

## Types

A type is indexed by its context and kind. Types are intrinsically
scoped and kinded: it's impossible to construct an ill-kinded
application and it's impossible to refer to a variable that is not in
scope.

A type is either a type variable, a pi type, a function type, a
lambda, an application, an iso-recursive type `μ`, a size, or a type
constant (base type). Note that recursive types range over an
arbitrary kind `k` which goes beyond standard iso-recursive types.

```
open import Data.String

data _⊢⋆_ : Ctx⋆ → Kind → Set where

  ` : Φ ∋⋆ J
      --------
    → Φ ⊢⋆ J

  Π : Φ ,⋆ K ⊢⋆ *
      -----------
    → Φ ⊢⋆ *

  _⇒_ : Φ ⊢⋆ *
      → Φ ⊢⋆ *
        ------
      → Φ ⊢⋆ *

  ƛ : Φ ,⋆ K ⊢⋆ J 
      -----------
    → Φ ⊢⋆ K ⇒ J

  _·_ : Φ ⊢⋆ K ⇒ J
      → Φ ⊢⋆ K
        ------
      → Φ ⊢⋆ J

  μ : Φ ⊢⋆ (K ⇒ *) ⇒ K ⇒ *
    → Φ ⊢⋆ K
      ---------------------
    → Φ ⊢⋆ *

  con : TyCon
        ------
      → Φ ⊢⋆ *
```

Let `A`, `B`, `C` range over types:
```
variable
  A A' B B' C C'  : Φ ⊢⋆ J
```
