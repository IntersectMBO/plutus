---
title: Untyped syntax
layout: page
---

```
module Untyped where
```

## Imports

```
open import Utils as U using (Maybe;nothing;just;maybeToEither;Either;inj₁;inj₂;Monad;DATA;List;[];_∷_;natToFin)
open Monad {{...}}
import Data.List as L

open import Scoped using (ScopeError;deBError)
open import Builtin using (Builtin;equals;decBuiltin)
open Builtin.Builtin

open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
open import Data.Nat using (ℕ;suc;zero;_<_;_<?_)
open import Data.Fin using (Fin;suc;zero;toℕ;fromℕ<)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Bool using (Bool;true;false;_∧_)
open import Data.Integer using (_+_;_-_;∣_∣;_≟_;ℤ) renaming (_*_ to _**_) -- TODO: remove unnecessary imports
open import Relation.Nullary using (does;yes;no)
open import Data.Integer.Show using (show)
open import Data.String using (String;_++_)
open import Data.Empty using (⊥)
open import Utils using (_×_;_,_)
open import RawU using (TagCon;Tag;decTagCon;TmCon;TyTag;Untyped;tmCon;tmCon2TagCon;tagCon2TmCon;⟦_⟧tag)
open import Builtin.Signature using (_⊢♯;integer;bool;string;pdata;bytestring;unit;bls12-381-g1-element;bls12-381-g2-element;bls12-381-mlresult)
open _⊢♯
open import Builtin.Constant.AtomicType using (AtomicTyCon)
open AtomicTyCon

open import Builtin.Constant.Type
open Untyped
```

## Well-scoped Syntax

This defines the syntax for UPLC and requires that it be "well scoped", which
is that only variables in the context are used. The context uses de Bruijn naming,
so the variables are numbered.

```
infixl 7 _·_

data _⊢ (n : ℕ) : Set where
  `   : Fin n → n ⊢
  ƛ   : suc n ⊢ → n ⊢
  _·_ : n ⊢ → n ⊢ → n ⊢
  force : n ⊢ → n ⊢
  delay : n ⊢ → n ⊢
  con : TmCon → n ⊢
  constr : (i : ℕ) → (xs : L.List (n ⊢)) → n ⊢
  case :  (t : n ⊢) → (ts : L.List (n ⊢)) → n ⊢
  builtin : (b : Builtin) → n ⊢
  error : n ⊢
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

{-# TERMINATING #-}
uglyTmConList : (t : TyTag) → ⟦ list t ⟧tag → String
uglyTmConList t [] = ""
uglyTmConList t (x ∷ []) = uglyTmCon (tmCon t x)
uglyTmConList t (x ∷ l ∷ ls) = uglyTmCon (tmCon t x) ++ " , " ++ (uglyTmConList t (l ∷ ls))

uglyTmCon (tmCon integer x)              = "(integer " ++ show x ++ ")"
uglyTmCon (tmCon bytestring x)           = "bytestring"
uglyTmCon (tmCon unit _)                 = "()"
uglyTmCon (tmCon string s)               = "(string " ++ s ++ ")"
uglyTmCon (tmCon bool false)             = "(bool false)"
uglyTmCon (tmCon bool true)              = "(bool true)"
uglyTmCon (tmCon pdata d)                = uglyDATA d
uglyTmCon (tmCon bls12-381-g1-element e) = "(bls12-381-g1-element ???)"  -- FIXME
uglyTmCon (tmCon bls12-381-g2-element e) = "(bls12-381-g2-element ???)"  -- FIXME
uglyTmCon (tmCon bls12-381-mlresult r)   = "(bls12-381-mlresult ???)"      -- FIXME
uglyTmCon (tmCon (array t) xs)            = "(array [ something ])" -- FIXME: https://github.com/IntersectMBO/plutus-private/issues/1603
uglyTmCon (tmCon (list t) xs)            = "(list [ " ++ (uglyTmConList t xs) ++ " ])"
uglyTmCon (tmCon (pair t u) (x , y))     = "(pair (" ++ uglyTmCon (tmCon t x) ++ " , " ++ uglyTmCon (tmCon u y) ++ ") )"

{-# FOREIGN GHC import qualified Data.Text as T #-}

postulate showNat : ℕ → String

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC showNat = T.pack . show #-}

uglyBuiltin : Builtin → String
uglyBuiltin addInteger = "addInteger"
uglyBuiltin _ = "other"
-- FIXME: This is boring but we should fill it in
-- if we are going to start using this
-- https://github.com/IntersectMBO/plutus-private/issues/1621

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

extricateUList : {n : ℕ} → L.List (n ⊢) → List Untyped
extricateU : {n : ℕ} → n ⊢ → Untyped
extricateU (` x)         = UVar (toℕ x)
extricateU (ƛ t)         = ULambda (extricateU t)
extricateU (t · u)       = UApp (extricateU t) (extricateU u)
extricateU (force t)     = UForce (extricateU t)
extricateU (delay t)     = UDelay (extricateU t)
extricateU (con c)       = UCon (tmCon2TagCon c)
extricateU (builtin b)   = UBuiltin b
extricateU error         = UError
extricateU (constr i L.[]) = UConstr i []
extricateU (constr i (x L.∷ xs)) = UConstr i (extricateU x ∷ extricateUList xs)
extricateU (case x xs)   = UCase (extricateU x) (extricateUList xs)

extricateUList L.[] = []
extricateUList (x L.∷ xs) = extricateU x ∷ extricateUList xs

extricateU0 : 0  ⊢ → Untyped
extricateU0 t = extricateU t

extG' : {X : Set} → (ℕ → Either ScopeError X) → ℕ → Either ScopeError (Maybe X)
extG' g zero    = return nothing
extG' g (suc n) = fmap just (g n)


scopeCheckUList : {n : ℕ} → List Untyped → Either ScopeError (L.List (n ⊢))
scopeCheckU : {n : ℕ} → Untyped → Either ScopeError (n ⊢)
scopeCheckU (UVar x)     = fmap ` (maybeToEither deBError (natToFin x))
scopeCheckU (ULambda t)  = fmap ƛ (scopeCheckU t)
scopeCheckU (UApp t u)   = do
  t ← scopeCheckU t
  u ← scopeCheckU u
  return (t · u)
scopeCheckU (UCon c)       = return (con (tagCon2TmCon c))
scopeCheckU UError         = return error
scopeCheckU (UBuiltin b)   = return (builtin b)
scopeCheckU (UDelay t)     = fmap delay (scopeCheckU t)
scopeCheckU (UForce t)     = fmap force (scopeCheckU t)
scopeCheckU (UConstr i ts) = fmap (constr i) (scopeCheckUList ts)
scopeCheckU (UCase t ts)   = do
                 u  ← scopeCheckU t
                 us ← scopeCheckUList ts
                 return (case u us)

scopeCheckUList [] = inj₂ L.[]
scopeCheckUList (x ∷ xs) = do
                 u  ← scopeCheckU x
                 us ← scopeCheckUList xs
                 return (u L.∷ us)

scopeCheckU0 : Untyped → Either ScopeError (0 ⊢)
scopeCheckU0 t = scopeCheckU t
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

## Haskell UPLC to Agda UPLC
```
buildDebruijnEncoding : {X : Set} → ℕ → Either ScopeError (Maybe X)
buildDebruijnEncoding x = extG' (λ _ → inj₁ deBError) x

```
Some useful functions for making integer literals.
```
open import Agda.Builtin.Int using (Int)

make-integer : RawU.TyTag
make-integer = RawU.tag2TyTag RawU.integer

con-integer : {n : ℕ} → ℕ → n ⊢
con-integer n = (con (tmCon make-integer (Int.pos n)))
