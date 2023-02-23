---
title: Signatures
layout: page
---

Module for abstract signatures of builtins:

This module defines signatures for characterizing the types of built-in functions.

The signatures defined in this module are abstract in the sense 
that they don't refer to any particular typing context or typing rule,
except for the minimal rule of guaranteeing well-formedness.

## Imports 

```
module Signature where

open import Data.Nat using (ℕ;zero;suc)
open import Data.Fin renaming (zero to Z; suc to S)
open import Data.List.NonEmpty using (List⁺;foldr)

open import Utils using (*)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z;S;Φ)
```

## Built-in compatible types 

The arguments of a built-in function can't be just any type, but are restricted 
to certain types, which in this file are called *built-in-compatible* types.

The built-in compatible types are either type constants, type variables, 
or type operators applied to built-in-compatible type.

The type of built-in-compatible types (_⊢♯) is indexed by the number of 
distinct type variables.
```
data _⊢♯ : ℕ → Set

open import Builtin.Constant.Type ℕ (_⊢♯) using (TyCon)

data _⊢♯ where
  -- a type variable
  ` : ∀ {n} → 
      Fin n
      --------
    → n ⊢♯

  -- a type constant or type operator applied to a built-in-compatible type
  con : ∀ {n} → 
      TyCon n
      ------
      → n ⊢♯
```

The list of arguments is a non-empty list of built-in compatible types.
It is indexed by the number of distinct type variables that may appear.

```

Args : ℕ → Set
Args n = List⁺ (n ⊢♯) 

```

## Signatures

A signature is given by
  1. The number (fv♯) of type variables that may appear
  2. A list of arguments
  3. A result type

```
record Sig : Set where 
   constructor sig
   field
     -- number of type variables
    fv♯ : ℕ   
     -- list of arguments
    args : Args fv♯
     -- type of result
    result : fv♯ ⊢♯

```

## Obtaining concrete types from signatures

Signatures represent abstract types which need to be made concrete in 
order to use them. The following modules may be instantiated to obtain 
a function `sig2type` which converts from an abstract into a concrete type.

The following parameters should be instantiated:

   1. the set `Ctx` over which types are indexed,
   2. the types `Ty` (indexed over `Ctx`),
   3. a function interpreting naturals as elements of `Ctx`,  
   4. a function interpreting variable indexes into types in `Ty,
   5. a way to insert a type constant as a type,
   6. the constructor for function types, and
   7. the constructor for Π types.
```
import Builtin.Constant.Type as T2
open T2.TyCon

module FromSig (Ctx : Set)
               (Ty : Ctx → Set) 
               (nat2Ctx : ℕ → Ctx) 
               (fin2Ty : ∀{n} → Fin n → Ty (nat2Ctx n))
               (mkTyCon : ∀{n} → T2.TyCon Ctx Ty (nat2Ctx n) → Ty (nat2Ctx n)) 
               (_⇒_ : ∀{n} → Ty (nat2Ctx n) → Ty (nat2Ctx n) → Ty (nat2Ctx n))
               (Π : ∀{n} → Ty (nat2Ctx (suc n)) → Ty (nat2Ctx n))
          where

    -- convert a built-in-compatible type into a Ty type
    ♯2* : ∀{n} → n ⊢♯ → Ty (nat2Ctx n)
    ♯2* (` x) = fin2Ty x
    ♯2* (con integer) = mkTyCon T2.integer
    ♯2* (con bytestring) = mkTyCon  T2.bytestring
    ♯2* (con string) = mkTyCon  T2.string
    ♯2* (con unit) = mkTyCon  T2.unit
    ♯2* (con bool) = mkTyCon  T2.bool
    ♯2* (con (list x)) = mkTyCon  (T2.list (♯2* x))
    ♯2* (con (pair x y)) = mkTyCon  (T2.pair (♯2* x) (♯2* y))
    ♯2* (con pdata) = mkTyCon  T2.pdata

    {- `sig2type-aux` takes a list of arguments and a result type, and produces
        a function that takes all arguments and returns the result type.

       sig2type-aux [ b₁ , b₂ , ... ,bₙ ] tᵣ = t₁ ⇒ t₂ ⇒ ... ⇒ tₙ ⇒ tᵣ
          where tᵢ = ♯2* bᵢ
    -}
    sig2type-aux : ∀{n} 
              → Args n 
              → Ty (nat2Ctx n) → Ty (nat2Ctx n)
    sig2type-aux xs = foldr (λ A xs res → (♯2* A) ⇒ (xs res)) (λ A res → ♯2* A ⇒ res) xs

    -- take a type and close its type variables using Π
    sig2type-aux2 : ∀{n} → Ty (nat2Ctx n) → Ty (nat2Ctx 0)
    sig2type-aux2 {zero} t = t
    sig2type-aux2 {suc n} t = sig2type-aux2 {n} (Π t)

    -- The main conversion function
    sig2type : Sig → Ty (nat2Ctx 0)
    sig2type (sig _ as res) = sig2type-aux2 (sig2type-aux as (♯2* res)) 
```

The parameter `Ctx` above is usually `Ctx⋆`.  In this case, the parameters
 `nat2Ctx` and  `fin2Ty` con be instantiated with the help of the following 
 auxiliary functions.

```
nat2Ctx⋆ : ℕ → Ctx⋆
nat2Ctx⋆ zero = ∅
nat2Ctx⋆ (suc n) = nat2Ctx⋆ n ,⋆ *

fin2∈⋆ : ∀{n} → Fin n → (nat2Ctx⋆ n) ∋⋆ *
fin2∈⋆ Z = Z
fin2∈⋆ (S x) = S (fin2∈⋆ x)
```