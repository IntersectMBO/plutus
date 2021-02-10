---
title: Untyped syntax
layout: page
---

```
module Untyped where
```

## Imports

```
open import Data.Nat
open import Data.Fin hiding (_≤_)
open import Data.Bool using (Bool;true;false)
open import Data.Integer hiding (suc;_≤_)
open import Data.String using (String) renaming (_++_ to _+++_)
open import Data.Char
open import Data.Sum
open import Data.Product renaming (_,_ to _,,_)
open import Relation.Nullary
open import Data.String
open import Data.Bool

open import Raw
open import Utils
open import Scoped using (ScopeError;deBError)
open import Builtin
```

## Term constants

Defined separetely here rather than using generic version used in the
typed syntax.

```
data TermCon : Set where
  integer    : ℤ → TermCon
  bytestring : ByteString → TermCon
  string     : String → TermCon
  bool       : Bool → TermCon
  char       : Char → TermCon
  unit       : TermCon
```

## Well-scoped Syntax

```
data _⊢ n : Set where
  `       : Fin n → n ⊢
  ƛ       : suc n ⊢ → n ⊢
  _·_     : n ⊢ → n ⊢ → n ⊢
  force   : n ⊢ → n ⊢
  delay   : n ⊢ → n ⊢
  con     : TermCon → n ⊢
  builtin : (b : Builtin) → n ⊢
  error   : n ⊢

variable
  n m o : ℕ
  t t' u u' : n ⊢
```

## Ugly printing for debugging

```
uglyFin : ∀{n} → Fin n → String
uglyFin zero = "0"
uglyFin (suc x) = "(S " +++ uglyFin x +++ ")"


uglyTermCon : TermCon → String
uglyTermCon (integer x) = "(integer " +++ Data.Integer.show x +++ ")"
uglyTermCon (bytestring x) = "bytestring"
uglyTermCon unit = "()"
uglyTermCon (string s) = "(string " +++ s +++ ")"
uglyTermCon (bool false) = "(bool " +++ "false" +++ ")"
uglyTermCon (bool true) = "(bool " +++ "true" +++ ")"
uglyTermCon (char c) = "(char)"

{-# FOREIGN GHC import qualified Data.Text as T #-}

postulate showNat : ℕ → String

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC showNat = T.pack . show #-}

uglyBuiltin : Builtin → String
uglyBuiltin addInteger = "addInteger"
uglyBuiltin _ = "other"

ugly : n ⊢ → String
ugly (` x) = "(` " +++ uglyFin x +++ ")"
ugly (ƛ t) = "(ƛ " +++ ugly t +++ ")"
ugly (t · u) = "( " +++ ugly t +++ " · " +++ ugly u +++ ")"
ugly (con c) = "(con " +++ uglyTermCon c +++ ")"
ugly (force t) = "(f0rce " +++ ugly t +++ ")"
ugly (delay t) = "(delay " +++ ugly t +++ ")"
ugly (builtin b) = "(builtin " +++ uglyBuiltin b +++ ")"
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
{-# COMPILE GHC TermCon = data UConstant (UConInt | UConBS | UConStr | UConBool | UConChar | UConUnit) #-}
```

## Scope checking

```
extricateU : n ⊢ → Untyped
extricateU (con c) = UCon c
extricateU (` x) = UVar (Data.Fin.toℕ x)
extricateU (ƛ t) = ULambda (extricateU t)
extricateU (t · u) = UApp (extricateU t) (extricateU u)
extricateU (force t) = UForce (extricateU t)
extricateU (delay t) = UDelay (extricateU t)
extricateU (builtin b) = UBuiltin b
extricateU error = UError

ℕtoFin : ℕ → Either ScopeError (Fin n)
ℕtoFin {zero}  _       = inj₁ deBError
ℕtoFin {suc m} zero    = return zero
ℕtoFin {suc m} (suc n) = fmap suc (ℕtoFin n)

scopeCheckU : Untyped → Either ScopeError (n ⊢)
scopeCheckU (UVar x)     = fmap ` (ℕtoFin x)
scopeCheckU (ULambda t)  = fmap ƛ (scopeCheckU t)
scopeCheckU (UApp t u)   = do
  t ← scopeCheckU t
  u ← scopeCheckU u
  return (t · u)
scopeCheckU (UCon c)     = return (con c)
scopeCheckU UError       = return error
scopeCheckU (UBuiltin b) = return (builtin b)
scopeCheckU (UDelay t)   = fmap delay (scopeCheckU t)
scopeCheckU (UForce t)   = fmap force (scopeCheckU t)
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
decUTermCon (char c) (char c') = true
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
```
