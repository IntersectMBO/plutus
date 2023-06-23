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

open import Data.Nat using (ℕ;zero;suc;_+_)
open import Data.Nat.Properties using (+-identityʳ;suc-injective)
open import Data.Fin using (Fin) renaming (zero to Z; suc to S)
open import Data.List using (List;[];_∷_;length)
open import Data.List.NonEmpty using (List⁺;foldr;_∷_;toList;reverse) renaming (length to length⁺)
open import Data.Product using (Σ;proj₁;proj₂) 
                  renaming (_,_ to _,,_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;sym;cong;trans;subst)

open import Utils using (Kind;♯;*;_⇒_;_∔_≣_;start;bubble;alldone;unique∔;_×_;∔2+) 
        renaming (List to UList)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z;S;Φ)
open import Builtin.Constant.AtomicType using (AtomicTyCon;⟦_⟧at)
open AtomicTyCon
open import Builtin.Constant.Type using (TyCon)
open TyCon
```

## Argument Types and Built-in Compatible Types 

The arguments of a built-in function can't be just any type, but are restricted 
to certain types, which in this file are called *argument* types.
They are either a variable of kind * (that is, ranging over any type) 
or a *built-in-compatible* type.

The built-in compatible types are either type constants of kind ♯, type variables, 
or type operators applied to built-in-compatible type.

The type of built-in-compatible types (_⊢♯) is indexed by the number of 
distinct type variables of kind ♯.
```
-- Builtin compatible types of kind ♯
data _⊢♯ : ℕ → Set where
  -- a type variable
  ` : ∀ {n♯} → 
      Fin n♯ 
      --------
    → n♯ ⊢♯

  -- a type constant 
  atomic : ∀ {n♯} 
      → AtomicTyCon 
        -----------
      → n♯ ⊢♯
  -- type operator applied to a built-in-compatible type
  list : ∀ {n♯}
      → n♯ ⊢♯ 
        -------
      → n♯ ⊢♯
  pair : ∀ {n♯}
      → n♯ ⊢♯ 
      → n♯ ⊢♯ 
        -------
      → n♯ ⊢♯

-- argument types are either a variable of kind * or a builtin compatible type
data _/_⊢⋆ : ℕ → ℕ → Set where
  -- a type variable of kind *
  ` : ∀ {n⋆ n♯} → 
      Fin n⋆ 
      --------
    → n⋆ / n♯ ⊢⋆
  -- a builtin compatible type
  _↑ : ∀ {n⋆ n♯} →
        n♯ ⊢♯ 
       -------
     → n⋆ / n♯ ⊢⋆

pattern integer              = atomic aInteger
pattern bytestring           = atomic aBytestring
pattern string               = atomic aString
pattern unit                 = atomic aUnit
pattern bool                 = atomic aBool
pattern pdata                = atomic aData
pattern bls12-381-g1-element = atomic aBls12-381-g1-element
pattern bls12-381-g2-element = atomic aBls12-381-g2-element
pattern bls12-381-mlresult   = atomic aBls12-381-mlresult
```

The list of arguments is a non-empty list of argument types.
It is indexed by the number of distinct type variables 
of kind ♯ and kind *  that may appear.

```

Args : ℕ → ℕ → Set
Args n⋆ n♯ = List⁺ (n⋆ / n♯ ⊢⋆) 

```

## Signatures

A signature is given by
  1. The number (fv⋆) of type variables of kind * that may appear
  2. The number (fv♯) of type variables of kind ♯ that may appear
  3. A list of arguments
  4. A result type

```
record Sig : Set where 
   constructor sig
   field
     -- number of type variables of kind *
    fv⋆ : ℕ  
     -- number of type variables of kind ♯
    fv♯ : ℕ     
     -- list of arguments
    args : Args fv⋆ fv♯
     -- type of result
    result : fv⋆ / fv♯ ⊢⋆

open Sig

-- number of arguments in a signature
args♯ : Sig → ℕ
args♯ σ = length⁺ (args σ)

-- number of free variables of either kind in a signature
fv : Sig → ℕ
fv σ = fv⋆ σ + fv♯ σ
```

### Auxiliary functions

The following functions help to:
 * mkCtx⋆ : build a context with a certain number of *-kinded and ♯-kinded 
   variables.
 * fin♯2∋⋆ and fin⋆2∋⋆ : variables for a context obtained from mkCtx⋆.

Note that we only need the number of variables of each kind because we always
 order them in a fixed way: first the * variables, and then the ♯ variables.
 This simplifies the treatment of variables and contexts, and in the context 
 of signatures, without losing generality.
```
mkCtx⋆ : ∀ (n⋆ n♯ : ℕ) → Ctx⋆
mkCtx⋆ zero     zero     = ∅
mkCtx⋆ zero     (suc n♯) = mkCtx⋆ zero n♯ ,⋆ ♯
mkCtx⋆ (suc n⋆) n♯       = mkCtx⋆ n⋆ n♯ ,⋆ *

fin♯2∋⋆ : ∀{n⋆ n♯} → Fin n♯ → (mkCtx⋆ n⋆ n♯) ∋⋆ ♯
fin♯2∋⋆ {zero} Z       = Z
fin♯2∋⋆ {suc n⋆} Z     = S (fin♯2∋⋆ Z)
fin♯2∋⋆ {zero} (S x)   = S (fin♯2∋⋆ x)
fin♯2∋⋆ {suc n⋆} (S x) = S (fin♯2∋⋆ (S x))

fin⋆2∋⋆ : ∀{n⋆ n♯} → Fin n⋆ → (mkCtx⋆ n⋆ n♯) ∋⋆ *
fin⋆2∋⋆ Z = Z
fin⋆2∋⋆ (S x) = S (fin⋆2∋⋆ x)
```  

## Obtaining concrete types from signatures

Signatures represent abstract types which need to be made concrete in 
order to use them. The following module may be instantiated to obtain 
a function `sig2type` which converts from an abstract into a concrete type.

### Module parameterised to allow for different notions of types.

The following parameters should be instantiated:

   1. the types `Ty` (indexed over `Ctx⋆` and `Kind`),
   2. the type of neutral types (indexed over `Ctx⋆` and `Kind`),
   3. a function interpreting variable into neutral types,
   4. the constructor for application,
   5. the constructor for type constant,
   6. a function inserting types of kind ♯ into types of kind *,
   7. the constructor for function types, and
   8. the constructor for Π types.

```
module FromSig (Ty : Ctx⋆ → Kind → Set) 
               (TyNe : Ctx⋆ → Kind → Set) 
               (ne : ∀{Φ K} → TyNe Φ K → Ty Φ K)
               (var : ∀{n⋆ n♯ K} → mkCtx⋆ n⋆ n♯ ∋⋆ K → TyNe (mkCtx⋆ n⋆ n♯) K)
               (_·_ : ∀{Φ K J} → TyNe Φ (K ⇒ J) → Ty Φ K → TyNe Φ J)
               (^ : ∀{Φ K} → TyCon K → TyNe Φ K) 
               (mkCon : ∀{Φ} → Ty Φ ♯ → Ty Φ *)
               (_⇒_ : ∀{Φ} → Ty Φ * → Ty Φ *  → Ty Φ *)
               (Π : ∀{Φ K} → Ty (Φ ,⋆ K) * → Ty Φ *)
          where
```

  The function mkTy constructs a type from an argument type. For that it 
  uses the function ⊢♯2TyNe♯ which constructs a neutral type from a 
  built-in compatible type.

```
    ⊢♯2TyNe♯ : ∀{n⋆ n♯} → n♯ ⊢♯ → TyNe (mkCtx⋆ n⋆ n♯) ♯
    ⊢♯2TyNe♯ (` x) =  var (fin♯2∋⋆ x)
    ⊢♯2TyNe♯ (atomic x) = ^ (atomic x)
    ⊢♯2TyNe♯ (list x)   = ^ list · ne (⊢♯2TyNe♯ x)
    ⊢♯2TyNe♯ (pair x y) = ((^ pair) · ne (⊢♯2TyNe♯ x)) · ne (⊢♯2TyNe♯ y)
    
    mkTy : ∀{n⋆ n♯} → n⋆ / n♯ ⊢⋆ → Ty (mkCtx⋆ n⋆ n♯) *
    mkTy (` x) = ne (var (fin⋆2∋⋆ x))
    mkTy (x ↑) = mkCon (ne (⊢♯2TyNe♯ x))
```

 `sig2type⇒` takes a list of arguments and a result type, and produces
        a function that takes all arguments and returns the result type.

   sig2type⇒ [ b₁ , b₂ , ... ,bₙ ] tᵣ = tₙ ⇒ ... ⇒ t₂ ⇒ t₁ ⇒ tᵣ
       where tᵢ = mkTy bᵢ
   
```
    sig2type⇒ : ∀{n⋆ n♯} 
              → List (n⋆ / n♯ ⊢⋆) 
              → Ty (mkCtx⋆ n⋆ n♯) * → Ty (mkCtx⋆ n⋆ n♯) *
    sig2type⇒ [] r = r
    sig2type⇒ (a ∷ as) r = sig2type⇒ as (mkTy a ⇒ r)
```

  `sig2typeΠ` adds as many Π as needed to close the type.

```
    sig2typeΠ : ∀{n⋆ n♯} → Ty (mkCtx⋆ n⋆ n♯) * → Ty (mkCtx⋆ 0 0) *
    sig2typeΠ {zero} {zero}   t = t
    sig2typeΠ {zero} {suc n♯} t = sig2typeΠ {zero} {n♯} (Π t)
    sig2typeΠ {suc n⋆} {n♯}   t = sig2typeΠ {n⋆} {n♯} (Π t)
```

   The main conversion function from a signature into a concrete type

```
    sig2type : Sig → Ty ∅ *
    sig2type (sig fv⋆ fv♯ as res) = sig2typeΠ (sig2type⇒ (toList as) (mkTy res))
```

### Types originating from a Signature

The types produced by a signature have a particular form: possibly 
some Π applications and then at least one function argument.

We define a predicate for concrete types of that shape as a datatype 
indexed by the concrete types.

```
    -- an : number of arguments to be added to the type 
    -- am : number of arguments expected
    -- at : total number of arguments
    -- tm : number of Π applied
    -- tn : number of Π yet to be applied
    -- tt: number of Π in the signature (fv♯)
    data SigTy : ∀{tn tm tt} → tn ∔ tm ≣ tt 
               → ∀{an am at} → an ∔ am ≣ at 
               → ∀{Φ} → Ty Φ * → Set where
       bresult  : ∀{tt} → {pt : tt ∔ 0 ≣ tt}
                → ∀{at} → {pa : at ∔ 0 ≣ at}
                → ∀{Φ} (A : Ty Φ *) 
                → SigTy pt pa A
       _B⇒_ : ∀{tn tt} → {pt : tn ∔ 0 ≣ tt }        -- all Π yet to be applied
            → ∀{an am at} → {pa : an ∔ suc am ≣ at} -- there is one more argument to add
            → ∀{Φ} → (A : Ty Φ *) 
                   → {B : Ty Φ *} 
            → SigTy pt (bubble pa) B 
            → SigTy pt pa (A ⇒ B)
       sucΠ : ∀{tn tm tt} → {pt : tn ∔ suc tm ≣ tt}
            → ∀{am an at} → {pa : an ∔ am ≣ at}
            → ∀{Φ K}{A : Ty (Φ ,⋆ K) *} 
            → SigTy (bubble pt) pa A 
            → SigTy pt pa (Π A)

```
   
   A `SigTy (0 ∔ tn ≣ tn) (0 ∔ at ≣ at) A` is a type that expects the total number of 
   type arguments `tn` and the total number of term arguments `at`.  

Every type obtained from a Signature σ using sig2type is a SigType.    

```    
    sig2SigTy⇒ : ∀{n⋆ n♯}{tt : ℕ}
             -- Additionally we could ask for the following condition to hold
             --  → (pn : n⋆ + n♯ ≡ tt)   
               → {pt : tt ∔ 0 ≣ tt}
               → (as : List (n⋆ / n♯ ⊢⋆))
               → ∀ {am at}(pa : length as ∔ am ≣ at)
               → {A : Ty (mkCtx⋆ n⋆ n♯) *} → (σA : SigTy pt pa A)
               → SigTy pt (start at) (sig2type⇒ as A)
    sig2SigTy⇒ []       (start _)   bty = bty
    sig2SigTy⇒ (a ∷ as) (bubble pa) bty = sig2SigTy⇒ as pa (mkTy a B⇒ bty)

    sig2SigTyΠ : ∀{n⋆ n♯ tn tm tt : ℕ} 
                    → (pn : n⋆ + n♯ ≡ tn) 
                    → (pt : tn ∔ tm ≣ tt) 
                    → ∀ {at}{pa : 0 ∔ at ≣ at}
                    → ∀{A : Ty (mkCtx⋆ n⋆ n♯) *} → SigTy pt pa A
                    → SigTy (start tt) pa (sig2typeΠ A)
    sig2SigTyΠ {zero} refl (start _)   bty = bty 
    sig2SigTyΠ {zero} refl (bubble pt) bty = sig2SigTyΠ refl pt (sucΠ bty)
    sig2SigTyΠ {suc n⋆} p  (bubble pt) bty = sig2SigTyΠ (suc-injective p) pt (sucΠ bty)
           
    -- From a signature obtain a signature type
    sig2SigTy : (σ : Sig) → SigTy (start (fv σ)) (start (args♯ σ)) (sig2type σ)
    sig2SigTy (sig n⋆ n♯ as r) =
                sig2SigTyΠ refl (alldone (n⋆ + n♯)) (sig2SigTy⇒ (toList as) (alldone (length⁺ as)) (bresult (mkTy r)))
 
    -- extract the concrete type from a signature type.
    sigTy2type : ∀{Φ tm tn tt an am at}{A : Ty Φ *} → {pt : tn ∔ tm ≣ tt} → {pa : an ∔ am ≣ at} → SigTy pt pa A → Ty Φ *
    sigTy2type {A = A} _ = A

    saturatedSigTy : ∀ (σ : Sig) → (A : Ty ∅ *) → Set
    saturatedSigTy σ A = SigTy (alldone (fv σ)) (alldone (args♯ σ)) A
```

## Conversion of Signature types

```
    convSigTy :
          ∀{tn tm tt} → {pt pt' : tn ∔ tm ≣ tt}
        → ∀{an am at} → {pa pa' : an ∔ am ≣ at}
        → ∀{n⋆ n♯}{A A' : Ty (mkCtx⋆ n⋆ n♯) *}
        → A ≡ A'
        → SigTy pt pa A
        → SigTy pt' pa' A'
    convSigTy {pt = pt} {pt'} {pa = pa} {pa'} refl sty rewrite unique∔ pt pt' | unique∔ pa pa' = sty
-- -}
```