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
open import Utils as U using (Maybe;nothing;just;Either;inj₁;inj₂;Monad;DATA;List;[];_∷_;_×_;_,_)
open import RawU using (Untyped)
open import Data.String using (String;_++_)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤;tt)
open import Function.Base using (id; _∘_ ; _∘′_; const; flip)
open Monad {{...}}
import IO.Primitive as IO using (return;_>>=_)
import Data.List as L
import VerifiedCompilation.UCaseOfCase as UCC
import VerifiedCompilation.UForceDelay as UFD
open import Data.Empty using (⊥)
open import Scoped using (ScopeError;deBError)
open import VerifiedCompilation.Equality using (DecEq)
import Relation.Binary as Binary using (Decidable)
open import VerifiedCompilation.UntypedTranslation using (Translation; Relation; translation?)
open import Reflection using (showTerm)
import Relation.Binary as Binary using (Decidable)
import Relation.Unary as Unary using (Decidable)
open import Relation.Binary.Core using (Rel)
open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (refl)
```

## Compiler certification component
```
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

aux : {X : Set} → List (Maybe X ⊢) -> List ((Maybe X ⊢) × (Maybe X ⊢))
aux [] = []
aux (x ∷ []) = (x , x) ∷ []
aux (x₁ ∷ (x₂ ∷ xs)) = (x₁ , x₂) ∷ aux (x₂ ∷ xs)

data Trace (R : Relation) : { X : Set } → List ((X ⊢) × (X ⊢)) → Set₁ where
  empty : {X : Set} → Trace R {X} []
  cons : {X : Set} {x x' : X ⊢} {xs : List ((X ⊢) × (X ⊢))} → R x x' → Trace R {X} xs → Trace R {X} ((x , x') ∷ xs)

isTrace? : {X : Set} {R : Relation} → Binary.Decidable (R {X}) → Unary.Decidable (Trace R {X})
isTrace? {X} {R} isR? [] = yes empty
isTrace? {X} {R} isR? ((x₁ , x₂) ∷ xs) with isTrace? {X} {R} isR? xs
... | no ¬p = no λ {(cons a as) → ¬p as}
... | yes p with isR? x₁ x₂
...   | no ¬p = no λ {(cons x x₁) → ¬p x}
...   | yes p₁ = yes (cons p₁ p)
  
traverseEitherList : {A B E : Set} → (A → Either E B) → List A → Either E (List B) 
traverseEitherList _ [] = inj₂ []
traverseEitherList f (x ∷ xs) with f x
... | inj₁ err = inj₁ err
... | inj₂ x' with traverseEitherList f xs
...     | inj₁ err = inj₁ err
...     | inj₂ resList = inj₂ (x' ∷ resList)

data IsTransformation : Relation where
  isCoC : {X : Set} → (ast ast' : X ⊢) → UCC.CoC ast ast' → IsTransformation ast ast'
  isFD : {X : Set} → (ast ast' : X ⊢) → UFD.FD ast ast' → IsTransformation ast ast'

isTransformation? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (IsTransformation {X})
isTransformation? ast₁ ast₂ with UCC.isCoC? ast₁ ast₂
... | bla with UFD.isFD? ast₁ ast₂
isTransformation? ast₁ ast₂ | no ¬p | no ¬p₁ = no λ {(isCoC .ast₁ .ast₂ x) → ¬p x
                                                   ; (isFD .ast₁ .ast₂ x) → ¬p₁ x}
isTransformation? ast₁ ast₂ | no ¬p | yes p = yes (isFD ast₁ ast₂ p)
isTransformation? ast₁ ast₂ | yes p | no ¬p = yes (isCoC ast₁ ast₂ p)
-- how can it be both? need to revisit this
isTransformation? ast₁ ast₂ | yes p | yes p₁ = yes (isCoC ast₁ ast₂ p)

showTranslation : {X : Set} {ast ast' : X ⊢} → Translation IsTransformation ast ast' → String
showTranslation (Translation.istranslation _ _ x) = "istranslation TODO"
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

-- showDec {X} result = showTerm (quoteTerm result)

showTrace : {X : Set} {xs : List ((X ⊢) × (X ⊢))} → Trace (Translation IsTransformation) xs → String
showTrace empty = "empty"
showTrace (cons x bla) = "(cons " ++ showTranslation x ++ showTrace bla ++ ")"

-- TODO: finish + write "show" functions for translations
serializeTraceProof : {X : Set} {xs : List ((X ⊢) × (X ⊢))} → Dec (Trace (Translation IsTransformation) xs) → String
serializeTraceProof (no ¬p) = "no" 
serializeTraceProof (yes p) = "yes " ++ showTrace p

certifier
  : {X : Set}
  → List Untyped
  → Unary.Decidable (Trace (Translation IsTransformation) {Maybe X})
  → Either ScopeError String
certifier {X} rawInput isRTrace? with traverseEitherList toWellScoped rawInput
... | inj₁ err = inj₁ err
... | inj₂ rawTrace = 
  let inputTrace = aux rawTrace
   in inj₂ (serializeTraceProof (isRTrace? inputTrace))

runCertifier : List Untyped → IO ⊤
runCertifier rawInput with certifier rawInput (isTrace? {Maybe ⊥} {Translation IsTransformation} (translation? isTransformation?))
... | inj₁ err = putStrLn "error" -- TODO: pretty print error
... | inj₂ result = putStrLn result
{-# COMPILE GHC runCertifier as runCertifier #-}
