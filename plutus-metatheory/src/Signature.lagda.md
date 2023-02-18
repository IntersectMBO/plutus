---
title: Signatures
layout: page
---

Module for abstract signatures of builtins:

We will define signatures as a list of arguments consisting of built-in-compatible types (_⊢♯_),
and a built-in-compatible type corresponding to a result.


```
module Signature where

open import Data.Nat using (ℕ;zero;suc)
open import Data.Fin renaming (zero to Z; suc to S)
open import Data.List.NonEmpty using (List⁺;foldr)

open import Utils using (*)
open import Type using (Ctx⋆;∅;_,⋆_;_⊢⋆_;_∋⋆_;Z;S;Φ)
```

## Built-in compatible types 

The built-in compatible types are either type constants, type variables, 
or type operators applied to built-in-compatible type.

The type is indexed by the number of type variables.

```
data _⊢♯ : ℕ → Set

open import Builtin.Constant.Type ℕ (_⊢♯) using (TyCon)
--open TyCon

data _⊢♯ where
  ` : ∀ {n} → 
      Fin n
      --------
    → n ⊢♯

  con : ∀ {n} → 
      TyCon n
      ------
      → n ⊢♯
```

The list of arguments is a non-empty list of built-in compatible types:

```

Args : ℕ → Set
Args n = List⁺ (n ⊢♯) 

```

## Signatures

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

variable 
 σ : Sig


-- TODO : Move this to Buitin.lagda.md
```
We can obtain types from a signature using the following auxiliary functions

```
nat2Ctx⋆ : ℕ → Ctx⋆
nat2Ctx⋆ zero = ∅
nat2Ctx⋆ (suc n) = nat2Ctx⋆ n ,⋆ *

fin2∈⋆ : ∀{n} → Fin n → (nat2Ctx⋆ n) ∋⋆ *
fin2∈⋆ Z = Z
fin2∈⋆ (S x) = S (fin2∈⋆ x)

module FromSig1 (Con : Set)(Ty : Con → Set) 
               (nat2Con : ℕ → Con) 
               (fin2Ty : ∀{n} → Fin n → Ty (nat2Con n))
               where

  import Builtin.Constant.Type Con Ty as T2
  open T2.TyCon

  module FromSig2 
           (mkTyCon : ∀{n} → T2.TyCon (nat2Con n) → Ty (nat2Con n)) 
           (_⇒_ : ∀{n} → Ty (nat2Con n) → Ty (nat2Con n) → Ty (nat2Con n))
           (Π : ∀{n} → Ty (nat2Con (suc n)) → Ty (nat2Con n))
          where

    ♯2* : ∀{n} → n ⊢♯ → Ty (nat2Con n)
    ♯2* (` x) = fin2Ty x
    ♯2* (con integer) = mkTyCon T2.integer
    ♯2* (con bytestring) = mkTyCon  T2.bytestring
    ♯2* (con string) = mkTyCon  T2.string
    ♯2* (con unit) = mkTyCon  T2.unit
    ♯2* (con bool) = mkTyCon  T2.bool
    ♯2* (con (list x)) = mkTyCon  (T2.list (♯2* x))
    ♯2* (con (pair x y)) = mkTyCon  (T2.pair (♯2* x) (♯2* y))
    ♯2* (con Data) = mkTyCon  T2.Data

    sig2type-aux : ∀{n} 
              → Args n 
              → Ty (nat2Con n) → Ty (nat2Con n)
    sig2type-aux xs = foldr (λ A xs res → (♯2* A) ⇒ (xs res)) (λ A res → ♯2* A ⇒ res) xs

    sig2type-aux2 : ∀{n} → Ty (nat2Con n) → Ty (nat2Con 0)
    sig2type-aux2 {zero} t = t
    sig2type-aux2 {suc n} t = sig2type-aux2 {n} (Π t)

    sig2type : Sig → Ty (nat2Con 0)
    sig2type (sig _ as res) = sig2type-aux2 (sig2type-aux as (♯2* res)) 
```
 