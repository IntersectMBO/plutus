---
title: Untyped syntax
layout: page
---

```
module Untyped where
```

## Imports

```
open import Utils as U using (Maybe;nothing;just;Either;inj₁;inj₂;Monad;DATA;List;[];_∷_)
open Monad {{...}}
import Data.List as L

open import Scoped using (ScopeError;deBError)
open import Builtin using (Builtin;equals;decBuiltin)
open Builtin.Builtin

open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
open import Data.Nat using (ℕ;suc;zero)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Bool using (Bool;true;false;_∧_)
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ) renaming (_*_ to _**_)
open import Relation.Nullary using (does;yes;no)
open import Data.Integer.Show using (show)
open import Data.String using (String;_++_)
open import Data.Empty using (⊥)
open import Utils using (_×_;_,_)
open import RawU using (TagCon;Tag;decTagCon;TmCon;TyTag;Untyped;tmCon;tmCon2TagCon;tagCon2TmCon)
open import Builtin.Signature using (_⊢♯;integer;bool;string;pdata;bytestring;unit;bls12-381-g1-element;bls12-381-g2-element;bls12-381-mlresult) 
open _⊢♯
open import Builtin.Constant.AtomicType using (AtomicTyCon)
open AtomicTyCon

open import Builtin.Constant.Type
open Untyped
```

## Well-scoped Syntax

```
data _⊢ (X : Set) : Set where
  `   : X → X ⊢
  ƛ   : Maybe X ⊢ → X ⊢
  _·_ : X ⊢ → X ⊢ → X ⊢
  force : X ⊢ → X ⊢
  delay : X ⊢ → X ⊢
  con : TmCon → X ⊢
  constr : (i : ℕ) → (xs : L.List (X ⊢)) → X ⊢
  case :  (t : X ⊢) → (ts : L.List (X ⊢)) → X ⊢
  builtin : (b : Builtin) → X ⊢
  error : X ⊢
```

```
variable
  t t' u u' : ∀{X} → X ⊢
```

## Debug printing

```
uglyDATA : DATA → String
uglyDATA d = "(DATA)"

uglyTmCon : TmCon → String
uglyTmCon (tmCon integer x)              = "(integer " ++ show x ++ ")"
uglyTmCon (tmCon bytestring x)           = "bytestring"
uglyTmCon (tmCon unit _)                 = "()"
uglyTmCon (tmCon string s)               = "(string " ++ s ++ ")"
uglyTmCon (tmCon bool false)             = "(bool " ++ "false" ++ ")"
uglyTmCon (tmCon bool true)              = "(bool " ++ "true" ++ ")"
uglyTmCon (tmCon pdata d)                = uglyDATA d
uglyTmCon (tmCon bls12-381-g1-element e) = "(bls12-381-g1-element ???)"  -- FIXME
uglyTmCon (tmCon bls12-381-g2-element e) = "(bls12-381-g2-element ???)"  -- FIXME
uglyTmCon (tmCon bls12-381-mlresult r)   = "(bls12-381-mlresult ???)"      -- FIXME
uglyTmCon (tmCon (pair t u) (x , y))     = "(pair " ++ uglyTmCon (tmCon t x) ++ " " ++ uglyTmCon (tmCon u y) ++ ")"
uglyTmCon (tmCon (list t) xs)            = "(list [ something ])"

{-# FOREIGN GHC import qualified Data.Text as T #-}

postulate showNat : ℕ → String

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC showNat = T.pack . show #-}

uglyBuiltin : Builtin → String
uglyBuiltin addInteger = "addInteger"
uglyBuiltin _ = "other"

uglyList : ∀{X} → L.List (X ⊢) → String
uglyList' : ∀{X} → L.List (X ⊢) → String
ugly : ∀{X} → X ⊢ → String
ugly (` x) = "(` var )"
ugly (ƛ t) = "(ƛ " ++ ugly t ++ ")"
ugly (t · u) = "( " ++ ugly t ++ " · " ++ ugly u ++ ")"
ugly (con c) = "(con " ++ uglyTmCon c ++ ")"
ugly (force t) = "(force " ++ ugly t ++ ")"
ugly (delay t) = "(delay " ++ ugly t ++ ")"
ugly (builtin b) = "(builtin " ++ uglyBuiltin b ++ ")"
ugly (constr i xs) = "(constr " ++ showℕ i ++ uglyList xs ++ ")"
ugly (case x ts) = "(case " ++ ugly x ++ " " ++ uglyList ts ++ ")"
ugly error = "error"

uglyList' L.[] = ""
uglyList' (x L.∷ xs) = ugly x ++" , "++ uglyList' xs

uglyList xs = "[" ++ uglyList' xs ++ "]"
```

## Scope checking and scope extrication

```
extG : {X : Set} → (X → ℕ) → Maybe X → ℕ
extG g (just x) = suc (g x)
extG g nothing  = 0

extricateUList : {X : Set} → (X → ℕ) → L.List (X ⊢) → List Untyped
extricateU : {X : Set} → (X → ℕ) → X ⊢ → Untyped
extricateU g (` x)         = UVar (g x)
extricateU g (ƛ t)         = ULambda (extricateU (extG g) t)
extricateU g (t · u)       = UApp (extricateU g t) (extricateU g u)
extricateU g (force t)     = UForce (extricateU g t)
extricateU g (delay t)     = UDelay (extricateU g t)
extricateU g (con c)       = UCon (tmCon2TagCon c)
extricateU g (builtin b)   = UBuiltin b
extricateU g error         = UError
extricateU g (constr i L.[]) = UConstr i []
extricateU g (constr i (x L.∷ xs)) = UConstr i (extricateU g x ∷ extricateUList g xs)
extricateU g (case x xs)   = UCase (extricateU g x) (extricateUList g xs)

extricateUList g L.[] = []
extricateUList g (x L.∷ xs) = extricateU g x ∷ extricateUList g xs

extricateU0 : ⊥  ⊢ → Untyped
extricateU0 t = extricateU (λ()) t

extG' : {X : Set} → (ℕ → Either ScopeError X) → ℕ → Either ScopeError (Maybe X)
extG' g zero    = return nothing
extG' g (suc n) = fmap just (g n)

scopeCheckUList : {X : Set}
            → (ℕ → Either ScopeError X) → List Untyped → Either ScopeError (L.List (X ⊢))
scopeCheckU : {X : Set}
            → (ℕ → Either ScopeError X) → Untyped → Either ScopeError (X ⊢)
scopeCheckU g (UVar x)     = fmap ` (g x)
scopeCheckU g (ULambda t)  = fmap ƛ (scopeCheckU (extG' g) t)
scopeCheckU g (UApp t u)   = do
  t ← scopeCheckU g t
  u ← scopeCheckU g u
  return (t · u)
scopeCheckU g (UCon c)       = return (con (tagCon2TmCon c))
scopeCheckU g UError         = return error
scopeCheckU g (UBuiltin b)   = return (builtin b)
scopeCheckU g (UDelay t)     = fmap delay (scopeCheckU g t)
scopeCheckU g (UForce t)     = fmap force (scopeCheckU g t)
scopeCheckU g (UConstr i ts) = fmap (constr i) (scopeCheckUList g ts)
scopeCheckU g (UCase t ts)   = do 
                 u  ← scopeCheckU g t 
                 us ← scopeCheckUList g ts
                 return (case u us)
                 
scopeCheckUList g [] = inj₂ L.[]
scopeCheckUList g (x ∷ xs) = do 
                 u  ← scopeCheckU g x 
                 us ← scopeCheckUList g xs
                 return (u L.∷ us)

scopeCheckU0 : Untyped → Either ScopeError (⊥ ⊢)
scopeCheckU0 t = scopeCheckU (λ _ → inj₁ deBError) t
```

## Equality checking for raw terms

Used to compare outputs in testing

```
decUTm : (t t' : Untyped) → Bool
decUTm (UVar x) (UVar x') = does (x Data.Nat.≟ x)
decUTm (ULambda t) (ULambda t') = decUTm t t'
decUTm (UApp t u) (UApp t' u') = decUTm t t' ∧ decUTm u u'
decUTm (UCon c) (UCon c') = decTagCon c c'
decUTm UError UError = true
decUTm (UBuiltin b) (UBuiltin b') = does (decBuiltin b b')
decUTm (UDelay t) (UDelay t') = decUTm t t'
decUTm (UForce t) (UForce t') = decUTm t t'
decUTm _ _ = false
```
