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
module Builtin.Signature where

open import Data.Nat using (ℕ;zero;suc)
open import Data.Nat.Properties using (+-identityʳ)
open import Data.Fin using (Fin) renaming (zero to Z; suc to S)
open import Data.List using (List;[];_∷_;length)
open import Data.List.NonEmpty using (List⁺;foldr;_∷_;toList;reverse) renaming (length to length⁺)
open import Data.Product using (Σ;proj₁;proj₂) renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;cong;trans;subst)

open import Utils using (*;_∔_≣_;start;bubble;alldone;unique∔)
open import Type using (Ctx⋆;_,⋆_;_⊢⋆_;_∋⋆_;Z;S;Φ)
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

open Sig

args♯ : Sig → ℕ
args♯ σ = length⁺ (args σ)
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

    -- The empty context
    ∅ : Ctx 
    ∅ = nat2Ctx 0
```

 `sig2type⇒` takes a list of arguments and a result type, and produces
        a function that takes all arguments and returns the result type.

   sig2type⇒ [ b₁ , b₂ , ... ,bₙ ] tᵣ = tₙ ⇒ ... ⇒ t₂ ⇒ t₁ ⇒ tᵣ
       where tᵢ = ♯2* bᵢ
   
```
    sig2type⇒ : ∀{n} 
              → List (n ⊢♯) 
              → Ty (nat2Ctx n) → Ty (nat2Ctx n)
    sig2type⇒ [] r = r
    sig2type⇒ (a ∷ as) r = sig2type⇒ as (♯2* a ⇒ r)
      --foldr (λ A xs res → (♯2* A) ⇒ (xs res)) (λ A res → ♯2* A ⇒ res) xs
```

  `sig2typeΠ` adds as many Π as needed to close the type.

```
    sig2typeΠ : ∀{n} → Ty (nat2Ctx n) → Ty (nat2Ctx 0)
    sig2typeΠ {zero} t = t
    sig2typeΠ {suc n} t = sig2typeΠ {n} (Π t)
```

   The main conversion function from a signature into a concrete type

```
    sig2type : Sig → Ty ∅
    sig2type (sig _ as res) = sig2typeΠ (sig2type⇒ (toList as) (♯2* res)) 
```

### Types originating from a Signature

The types produced by a signature have a particular form: possibly 
some Π applications and then at least one function argument.

We define a predicate for concrete types of that shape as a datatype 
indexed by the concrete types

```
    -- an : number of arguments to be added to the type 
    -- am : number of arguments expected
    -- at : total number of arguments
    -- tm : number of Π applied
    -- tn : number of Π yet to be applied
    -- tt: number of Π in the signature (fv♯)
    data SigTy : ∀{tn tm tt} → tn ∔ tm ≣ tt 
               → ∀{an am at} → an ∔ am ≣ at 
               → ∀{n} → Ty (nat2Ctx n) → Set where
       bresult  : ∀{tt} → {pt : tt ∔ 0 ≣ tt}
                → ∀{at} → {pa : at ∔ 0 ≣ at}
                → ∀{n} (A : Ty (nat2Ctx n)) 
                → SigTy pt pa A
       _B⇒_ : ∀{tn tt} → {pt : tn ∔ 0 ≣ tt }        -- all Π yet to be applied
            → ∀{an am at} → {pa : an ∔ suc am ≣ at} -- there is one more argument to add
            → ∀{n} → (A : Ty (nat2Ctx n)) 
                   → {B : Ty (nat2Ctx n)} 
            → SigTy pt (bubble pa) B 
            → SigTy pt pa (A ⇒ B)
       sucΠ : ∀{tn tm tt} → {pt : tn ∔ suc tm ≣ tt}
            → ∀{am an at} → {pa : an ∔ am ≣ at}
            → ∀{n}{A : Ty (nat2Ctx (suc n))} 
            → SigTy (bubble pt) pa A 
            → SigTy pt pa (Π A)

```
   
   A `SigTy (0 ∔ tn ≣ tn) at A` is a type that expects the total number of 
   type arguments `tn` and the total number of term arguments `at`.  

## Conversion from a Signature to a SigType    

```    
    sig2SigTy⇒ : ∀{tt : ℕ} → {pt : tt ∔ 0 ≣ tt}
               → (as : List (tt ⊢♯))
               → ∀ {am at}(pa : length as ∔ am ≣ at)
               → {A : Ty (nat2Ctx tt)} → (σA : SigTy pt pa A)
               → SigTy pt (start at) (sig2type⇒ as A)
    sig2SigTy⇒ [] (start _) bty = bty
    sig2SigTy⇒ (a ∷ as) (bubble pa) bty = sig2SigTy⇒ as pa (♯2* a B⇒ bty)


    sig2SigTyΠ : ∀{tn tm tt : ℕ} → (pt : tn ∔ tm ≣ tt) 
                    → ∀ {at}{pa : 0 ∔ at ≣ at}
                    → ∀{A : Ty (nat2Ctx tn)} → SigTy pt pa A
                    → SigTy (start tt) pa (sig2typeΠ A)
    sig2SigTyΠ (start _) bty = bty
    sig2SigTyΠ (bubble pt) bty = sig2SigTyΠ pt (sucΠ bty)
                        
    -- From a signature obtain a signature type
    sig2SigTy : (σ : Sig) → SigTy (start (fv♯ σ)) (start (args♯ σ)) (sig2type σ)
    sig2SigTy (sig n as r) =
                sig2SigTyΠ (alldone n) (sig2SigTy⇒ (toList as) (alldone (length⁺ as)) (bresult (♯2* r)))
 
    -- extract the concrete type from a signature type.
    sigTy2type : ∀{n tm tn tt an am at}{A : Ty (nat2Ctx n)} → {pt : tn ∔ tm ≣ tt} → {pa : an ∔ am ≣ at} → SigTy pt pa A → Ty (nat2Ctx n)
    sigTy2type {A = A} _ = A

    saturatedSigTy : ∀ (σ : Sig) → (A : Ty ∅) → Set
    saturatedSigTy σ A = SigTy (alldone (fv♯ σ)) (alldone (args♯ σ)) A
```

## Conversion of Signature types

```
    convSigTy :
          ∀{tn tm tt} → {pt pt' : tn ∔ tm ≣ tt}
        → ∀{an am at} → {pa pa' : an ∔ am ≣ at}
        → ∀{n}{A A' : Ty (nat2Ctx n)}
        → A ≡ A'
        → SigTy pt pa A
        → SigTy pt' pa' A'
    convSigTy {pt = pt} {pt'} {pa = pa} {pa'} refl sty rewrite unique∔ pt pt' | unique∔ pa pa' = sty
-- -}
```

## Auxiliary functions

The parameter `Ctx` above is usually `Ctx⋆`.  In this case, the parameters
 `nat2Ctx` and  `fin2Ty` can be instantiated with the help of the following 
 auxiliary functions.

```
nat2Ctx⋆ : ℕ → Ctx⋆
nat2Ctx⋆ zero = Ctx⋆.∅
nat2Ctx⋆ (suc n) = nat2Ctx⋆ n ,⋆ *

fin2∈⋆ : ∀{n} → Fin n → (nat2Ctx⋆ n) ∋⋆ *
fin2∈⋆ Z = Z
fin2∈⋆ (S x) = S (fin2∈⋆ x)
```  