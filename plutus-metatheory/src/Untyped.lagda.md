---
title: Untyped syntax
layout: page
---

```
{-# OPTIONS --type-in-type #-}
```

```
module Untyped where
```

## Imports

```
open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
open import Data.Nat using (ℕ;suc;zero)
open import Data.Bool using (Bool;true;false;_∧_)
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ) renaming (_*_ to _**_)
open import Data.Integer.Show using (show)
open import Data.String using (String;_++_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes;no;¬_;does)

open import Utils as U using (Maybe;nothing;just;Either;inj₁;inj₂;Monad;DATA;List;[];_∷_;eqDATA)
open import Utils using (_×_;_,_)
open Monad {{...}}

open import Scoped using (ScopeError;deBError)
open import Builtin using (Builtin;equals;decBuiltin)
open Builtin.Builtin

open import RawU using (TmCon;tmcon;Untyped;TyTag;decTag)
open TyTag
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

uglyList : List String → String
uglyList [] = ""
uglyList (x ∷ []) = x
uglyList (x ∷ xs) = x ++ "," ++ uglyList xs

uglyPair : DATA × DATA → String
uglyPair (x , y) = "("++ uglyDATA x ++ "," ++ uglyDATA y ++")"

uglyTermCon : TmCon → String
uglyTermCon (tmcon integer x) = "(integer " ++ show x ++ ")"
uglyTermCon (tmcon bytestring x) = "bytestring"
uglyTermCon (tmcon unit tt) = "()"
uglyTermCon (tmcon string s) = "(string " ++ s ++ ")"
uglyTermCon (tmcon bool false) = "(bool " ++ "false" ++ ")"
uglyTermCon (tmcon bool true) = "(bool " ++ "true" ++ ")"
uglyTermCon (tmcon (pair tx ty) (x , y)) = "(pair " ++ uglyTermCon (tmcon tx x) ++ " " ++ uglyTermCon (tmcon ty y) ++ ")"
--uglyTermCon (tmcon (list _) xs) = "(list [" ++ uglyList (map uglyTermCon xs) ++ "])"
uglyTermCon (tmcon (list _) xs)  = "(list)"
uglyTermCon (tmcon pdata d) = "(DATA)"



{-# FOREIGN GHC import qualified Data.Text as T #-}

postulate showNat : ℕ → String

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC showNat = T.pack . show #-}

uglyBuiltin : Builtin → String
uglyBuiltin addInteger = "addInteger"
uglyBuiltin _ = "other"

ugly : ∀{X} → X ⊢ → String
ugly (` x) = "(` var )"
ugly (ƛ t) = "(ƛ " ++ ugly t ++ ")"
ugly (t · u) = "( " ++ ugly t ++ " · " ++ ugly u ++ ")"
ugly (con c) = "(con " ++ uglyTermCon c ++ ")"
ugly (force t) = "(force " ++ ugly t ++ ")"
ugly (delay t) = "(delay " ++ ugly t ++ ")"
ugly (builtin b) = "(builtin " ++ uglyBuiltin b ++ ")"
ugly error = "error"
```

## Scope checking and scope extrication

```
extG : {X : Set} → (X → ℕ) → Maybe X → ℕ
extG g (just x) = suc (g x)
extG g nothing  = 0

extricateU : {X : Set} → (X → ℕ) → X ⊢ → Untyped
extricateU g (` x)       = UVar (g x)
extricateU g (ƛ t)       = ULambda (extricateU (extG g) t)
extricateU g (t · u)     = UApp (extricateU g t) (extricateU g u)
extricateU g (force t)   = UForce (extricateU g t)
extricateU g (delay t)   = UDelay (extricateU g t)
extricateU g (con c)     = UCon c
extricateU g (builtin b) = UBuiltin b
extricateU g error       = UError

extricateU0 : ⊥  ⊢ → Untyped
extricateU0 t = extricateU (λ()) t

extG' : {X : Set} → (ℕ → Either ScopeError X) → ℕ → Either ScopeError (Maybe X)
extG' g zero    = return nothing
extG' g (suc n) = fmap just (g n)

scopeCheckU : {X : Set}
            → (ℕ → Either ScopeError X) → Untyped → Either ScopeError (X ⊢)
scopeCheckU g (UVar x)     = fmap ` (g x)
scopeCheckU g (ULambda t)  = fmap ƛ (scopeCheckU (extG' g) t)
scopeCheckU g (UApp t u)   = do
  t ← scopeCheckU g t
  u ← scopeCheckU g u
  return (t · u)
scopeCheckU g (UCon c)     = return (con c)
scopeCheckU g UError       = return error
scopeCheckU g (UBuiltin b) = return (builtin b)
scopeCheckU g (UDelay t)   = fmap delay (scopeCheckU g t)
scopeCheckU g (UForce t)   = fmap force (scopeCheckU g t)

scopeCheckU0 : Untyped → Either ScopeError (⊥ ⊢)
scopeCheckU0 t = scopeCheckU (λ _ → inj₁ deBError) t
```

## Equality checking for raw terms

Used to compare outputs in testing

```
decUTermCon : (C C' : TmCon) → Bool
decUTermCon (tmcon tx x) (tmcon ty y) with decTag tx ty
decUTermCon (tmcon tx x) (tmcon ty y) | no ¬p = false
decUTermCon (tmcon integer x) (tmcon .integer y) | yes refl = does (x  Data.Integer.≟ y)
decUTermCon (tmcon bytestring x) (tmcon .bytestring y) | yes refl = equals x y
decUTermCon (tmcon string x) (tmcon .string y) | yes refl = does (x Data.String.≟  y)
decUTermCon (tmcon bool x) (tmcon .bool y) | yes refl = does (x Data.Bool.≟ y)
decUTermCon (tmcon unit x) (tmcon .unit y) | yes refl = true
decUTermCon (tmcon pdata x) (tmcon .pdata y) | yes refl = eqDATA x y
decUTermCon (tmcon (pair tx ty) (x , y)) (tmcon .(pair tx ty) (x' , y')) | yes refl = false
   -- TODO  (decUTermCon (tmcon tx x) (tmcon tx x')) ∧ (decUTermCon (tmcon ty y) (tmcon ty y'))
decUTermCon (tmcon (list tx) x) (tmcon .(list tx) y) | yes refl = false --TODO

{-
... | integer = does (x  Data.Integer.≟ y)
... | bytestring =  equals x y  
... | string = does (x Data.String.≟  y)
... | bool = does (x Data.Bool.≟ y)
... | unit = true
... | pdata = eqDATA x y
... | list t = false --TODO
decUTermCon (tmcon .(pair t u) (x , x')) (tmcon .(pair t u) (y , y')) | yes refl | pair t u =
  (decUTermCon (tmcon t x) (tmcon t y)) ∧ (decUTermCon (tmcon u x') (tmcon u y'))
-}
{- with x | y
... | x₁ , x₂ | y₁ , y₂ = (decUTermCon (tmcon t x₁) (tmcon t y₁)) ∧ (decUTermCon (tmcon u x₂) (tmcon u y₂))
-}

decUTm : (t t' : Untyped) → Bool
decUTm (UVar x) (UVar x') with x Data.Nat.≟ x
... | yes p = true
... | no ¬p = false
decUTm (ULambda t) (ULambda t') = decUTm t t'
decUTm (UApp t u) (UApp t' u') = decUTm t t' ∧ decUTm u u'
decUTm (UCon c) (UCon c') = decUTermCon c c'
decUTm UError UError = true
decUTm (UBuiltin b) (UBuiltin b') = decBuiltin b b'
decUTm (UDelay t) (UDelay t') = decUTm t t'
decUTm (UForce t) (UForce t') = decUTm t t'
decUTm _ _ = false
```
