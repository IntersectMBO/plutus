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

open import Scoped using (ScopeError;deBError)
open import Builtin using (Builtin;equals;decBuiltin)
open Builtin.Builtin

open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
open import Data.Nat using (ℕ;suc;zero)
open import Data.Bool using (Bool;true;false;_∧_)
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ) renaming (_*_ to _**_)
open import Relation.Nullary using (does;yes;no)
open import Data.Integer.Show using (show)
open import Data.String using (String;_++_)
open import Data.Empty using (⊥)
open import Utils using (_×_;_,_)
open import RawU using (TagCon;Tag;decTagCon;TmCon;TyTag;Untyped;tmCon;tmCon2TagCon;tagCon2TmCon)
open import Builtin.Signature using (_⊢♯;con) 
open import Builtin.Constant.Type ℕ (_⊢♯)
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

uglyTmCon : TmCon → String
uglyTmCon (tmCon (con integer) x) = "(integer " ++ show x ++ ")"
uglyTmCon (tmCon (con bytestring) x) = "bytestring"
uglyTmCon (tmCon (con unit) _)  = "()"
uglyTmCon (tmCon (con string) s) = "(string " ++ s ++ ")"
uglyTmCon (tmCon (con bool) false) = "(bool " ++ "false" ++ ")"
uglyTmCon (tmCon (con bool) true) = "(bool " ++ "true" ++ ")"
uglyTmCon (tmCon (con pdata) d) = uglyDATA d
uglyTmCon (tmCon (con (pair t u)) (x , y)) = "(pair " ++ uglyTmCon (tmCon t x) ++ " " ++ uglyTmCon (tmCon u y) ++ ")"
uglyTmCon (tmCon (con (list t)) xs) = "(list [ something ])"



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
ugly (con c) = "(con " ++ uglyTmCon c ++ ")"
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
extricateU g (con c)     = UCon (tmCon2TagCon c)
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
scopeCheckU g (UCon c)     = return (con (tagCon2TmCon c))
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
