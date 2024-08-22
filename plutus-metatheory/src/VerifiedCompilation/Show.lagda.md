---
title: VerifiedCompilation.Show
layout: page
---

# Show functions for VerifiedCompilation modules

```
module VerifiedCompilation.Show where

```
## Imports

```
open import VerifiedCompilation.UntypedTranslation using (Translation; Relation; translation?)
open import Untyped using (_⊢)
open import Data.String using (String;_++_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Utils as U using (Maybe;nothing;just)

open import VerifiedCompilation.UForceDelay using (FD; forcefd; delayfd; lastdelay; multiappliedfd; multiabstractfd)
open import VerifiedCompilation.UCaseOfCase using (CoC; isCoC)

```
## Instance Arguments
```
record VCShow (R : Relation) : Set₁ where
  field show : {X : Set} {x x' : X ⊢} → R x x' → String
open VCShow {{...}} public

showTranslation : {X : Set} {ast ast' : X ⊢} → {R : Relation}{{ _ : VCShow R}} → Translation R ast ast' → String
showTranslation (Translation.istranslation _ _ p) = "(istranslation " ++ show p ++ ")"
showTranslation Translation.var = "var"
showTranslation (Translation.ƛ t) = "(ƛ " ++ showTranslation t ++ ")"
showTranslation (Translation.app t t₁) = "(app " ++ showTranslation t ++ " " ++ showTranslation t₁ ++ ")"
showTranslation (Translation.force t) = "(force " ++ showTranslation t ++ ")"
showTranslation (Translation.delay t) = "(delay " ++ showTranslation t ++ ")"
showTranslation Translation.con = "con"
showTranslation (Translation.constr x) = "(constr TODO)"
showTranslation (Translation.case x t) = "(case TODO " ++ showTranslation t ++ ")"
showTranslation Translation.builtin = "builtin"
showTranslation Translation.error = "error"

```
## Individual Translation Show Instances

Many of the translation relations refer back to Translation, whose `show` function above
requires `VCShow` instances, so we declare the functions and make them instances
before providing the function definitions.
```

variable
  X : Set
  x x' : X ⊢
fdShow : {n nₐ : ℕ} → FD n nₐ x x' → String
cocShow : CoC x x' → String

instance
  VCShow-UFD : {n nₐ : ℕ} → VCShow (FD n nₐ)
  VCShow-UFD .show = fdShow
  VCShow-UCoC : VCShow CoC
  VCShow-UCoC .show = cocShow

{-# TERMINATING #-}
fdShow (forcefd n nₐ x x' p) = "(forcefd " ++ showℕ n ++ " " ++ showℕ nₐ ++ " " ++ fdShow p ++ ")"
fdShow (delayfd n nₐ x x' p) = "(delayfd " ++ showℕ n ++ " " ++ showℕ nₐ ++ " " ++ fdShow p ++ ")"
fdShow (lastdelay n nₐ x x' p) = "(lastdelay " ++ showℕ n ++ " " ++ showℕ nₐ ++ " " ++ showTranslation p ++ ")"
fdShow (multiappliedfd n nₐ x y x' y' p₁ p₂) = "(multiappliedfd " ++ showℕ n ++ " " ++ showℕ nₐ ++ " " ++ showTranslation p₁ ++ " " ++ fdShow p₂ ++ ")"
fdShow (multiabstractfd n nₐ x x' p) = "(multiabstractfd " ++ showℕ n ++ " " ++ showℕ nₐ ++ " " ++ fdShow p ++ ")"

-- FIXME: This will need pointwise Translation stuff, which is easy but... effort.
cocShow (isCoC b tn fn tt tt' ft ft' alts alts' x x₁ x₂) = "(isCoC TODO)"



```
