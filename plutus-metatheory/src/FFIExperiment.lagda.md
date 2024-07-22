---
title: FFIExperiment
layout: page
---
```
module FFIExperiment where
```

## Imports

```
import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)
open import Untyped
open import Utils as U using (Maybe;nothing;just;Either;inj₁;inj₂;Monad;DATA;List;[];_∷_)
open import RawU using (Untyped)
open import Data.String using (String;_++_)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤;tt)
open import Function.Base using (id; _∘_ ; _∘′_; const; flip)
open Monad {{...}}
import IO.Primitive as IO using (return;_>>=_)
import Data.List as L
import VerifiedCompilation.UCaseOfCase as UCC
open import Data.Empty using (⊥)
open import Scoped using (ScopeError;deBError)
open import VerifiedCompilation.Equality using (DecEq)
import Relation.Binary as Binary using (Decidable)
open import VerifiedCompilation.UntypedTranslation using (Translation)
open import Reflection using (showTerm)
```

## Compiler certification component
```
postulate
  -- This should actually return a Dec of some type representing
  -- a trace of ASTs which are in the transition relation one-by-one
  something : {X : Set} → List (X ⊢) → Dec (X ⊢ )
  -- This should take the result from the above and transform it
  -- into a string which could potentially be loaded back into Agda
  serializeProof : {X : Set} → Dec (X ⊢) → String

parseASTs : {X : Set} → List Untyped → Maybe (List (Maybe X ⊢))
parseASTs [] = nothing
parseASTs (x ∷ xs) with toWellScoped x 
...                | inj₁ _ = nothing
...                | inj₂ t with parseASTs xs
...                         | nothing = nothing
...                         | just ts = just (t ∷ ts)

postulate
  -- we will probably want hPutStrLn instead, to write to a file
  -- handle
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as TextIO #-}
{-# COMPILE GHC putStrLn = TextIO.putStrLn #-}

postulate
  exitFailure : IO ⊤
  exitSuccess : IO ⊤

{-# FOREIGN GHC import System.Exit #-}
{-# COMPILE GHC exitSuccess = exitSuccess #-}
{-# COMPILE GHC exitFailure = exitFailure #-}

instance
  IOMonad : Monad IO
  IOMonad = record { return = IO.return; _>>=_ = IO._>>=_ }

postulate
  showUntyped : Untyped → String
{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC showUntyped = Text.pack . show #-}

toWellScoped' : Untyped → Either ScopeError (Maybe ⊥ ⊢)
toWellScoped' = toWellScoped

showTranslation : {X : Set} {{_ : DecEq X}} {ast ast' : X ⊢} → Translation UCC.CoC ast ast' → String
showTranslation (Translation.istranslation _ _ x) = "istranslation TODO"
showTranslation Translation.var = "var"
showTranslation (Translation.ƛ t) = "(ƛ " ++ showTranslation t ++ ")"
showTranslation (Translation.app t t₁) = "(app " ++ showTranslation t ++ " " ++ showTranslation t₁ ++ ")"
showTranslation (Translation.force t) = "(force " ++ showTranslation t ++ ")"
showTranslation (Translation.delay t) = "(delay " ++ showTranslation t ++ ")"
showTranslation Translation.con = "con"
showTranslation (Translation.constr x) = "(constr TODO)"
showTranslation (Translation.case x t) = "case TODO " ++ showTranslation t ++ ")"
showTranslation Translation.builtin = "builtin"
showTranslation Translation.error = "error"

-- TODO: unparse proof
showDec : {X : Set} {{_ : DecEq X}} {ast ast' : X ⊢} → Dec (Translation UCC.CoC ast ast') → String
-- showDec {X} result = showTerm (quoteTerm result)
showDec {X} (yes refl) = "yes" ++ showTranslation refl
showDec {X} (no ¬refl) = "no"

-- TODO: write dec for a trace of ASTs
runCertifier : List Untyped → IO ⊤
runCertifier [] = putStrLn "No ASTs"
runCertifier (x ∷ xs) with toWellScoped' x
...                | inj₁ _ = putStrLn "Can't parse AST"
...                | inj₂ t =
                      let result = UCC.isUntypedCaseOfCase? t t
                       in do
                        putStrLn (showDec result)
                        runCertifier xs
{-# COMPILE GHC runCertifier as runCertifier #-}
