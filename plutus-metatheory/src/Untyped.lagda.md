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
open import Utils using (Maybe;nothing;just;Either;inj₁;inj₂;Monad;TermCon)
open Monad {{...}}
open TermCon

open import Scoped using (ScopeError;deBError)
open import Builtin using (Builtin;equals)
open Builtin.Builtin

open import Raw using (decBuiltin)

open import Agda.Builtin.String using (primStringFromList; primStringAppend; primStringEquality)
open import Data.Nat using (ℕ;suc;zero)
open import Data.Bool using (Bool;true;false;_∧_)
open import Data.Integer using (_<?_;_+_;_-_;∣_∣;_≤?_;_≟_;ℤ) renaming (_*_ to _**_)
open import Data.List using ([];_∷_)
open import Relation.Nullary using (yes;no)
open import Data.Integer.Show using (show)
open import Data.String using (String;_++_)
open import Data.Empty using (⊥)
```

## Well-scoped Syntax

```
data _⊢ (X : Set) : Set where
  `   : X → X ⊢
  ƛ   : Maybe X ⊢ → X ⊢
  _·_ : X ⊢ → X ⊢ → X ⊢
  force : X ⊢ → X ⊢
  delay : X ⊢ → X ⊢
  con : TermCon → X ⊢
  builtin : (b : Builtin) → X ⊢
  error : X ⊢
```

```
variable
  t t' u u' : ∀{X} → X ⊢
```

## Debug printing

```
uglyTermCon : TermCon → String
uglyTermCon (integer x) = "(integer " ++ show x ++ ")"
uglyTermCon (bytestring x) = "bytestring"
uglyTermCon unit = "()"
uglyTermCon (string s) = "(string " ++ s ++ ")"
uglyTermCon (bool false) = "(bool " ++ "false" ++ ")"
uglyTermCon (bool true) = "(bool " ++ "true" ++ ")"
uglyTermCon (pdata d) = "(DATA)"
uglyTermCon (bls12-381-g1-element e) = "(bls12-381-g1-element)"
uglyTermCon (bls12-381-g2-element e) = "(bls12-381-g2-element)"
uglyTermCon (bls12-381-mlresult r) = "(bls12-381-mlresult)"

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
ugly (force t) = "(f0rce " ++ ugly t ++ ")"
ugly (delay t) = "(delay " ++ ugly t ++ ")"
ugly (builtin b) = "(builtin " ++ uglyBuiltin b ++ ")"
ugly error = "error"
```

## Raw syntax

This version is not intrinsically well-scoped. It's an easy to work
with rendering of the untyped plutus-core syntax.

```
data Untyped : Set where
  UVar : ℕ → Untyped
  ULambda : Untyped → Untyped
  UApp : Untyped → Untyped → Untyped
  UCon : TermCon → Untyped
  UError : Untyped
  UBuiltin : Builtin → Untyped
  UDelay : Untyped → Untyped
  UForce : Untyped → Untyped

{-# FOREIGN GHC import Untyped #-}
{-# COMPILE GHC Untyped = data UTerm (UVar | ULambda  | UApp | UCon | UError | UBuiltin | UDelay | UForce) #-}
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
decUTermCon : (C C' : TermCon) → Bool
decUTermCon (integer i) (integer i') with i Data.Integer.≟ i'
... | yes p = true
... | no ¬p = false
decUTermCon (bytestring b) (bytestring b') with equals b b'
decUTermCon (bytestring b) (bytestring b') | false = false
decUTermCon (bytestring b) (bytestring b') | true = true
decUTermCon (string s) (string s') with s Data.String.≟ s'
... | yes p = true
... | no ¬p = false
decUTermCon (bool b) (bool b') with b Data.Bool.≟ b'
... | yes p = true
... | no ¬p = false
decUTermCon unit unit = true
decUTermCon _ _ = false

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
