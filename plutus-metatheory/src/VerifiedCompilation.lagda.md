---
title: VerifiedCompilation
layout: page
---
# Verified Compilation

## Introduction 

The verified compilation project is a formalization of the Untyped Plutus Core compiler optimisation transformations in Agda.
The goal is to generate a formal proof that the optimisation component of the compiler has transformed the input program correctly
with respect to the Agda specification (*). Our approach is based on Jacco Krijnen's work on
[Translation certification for smart contracts](https://www.sciencedirect.com/science/article/pii/S0167642323001338).


(*) **Note**: The current implementation does not guarantee corectness in the sense of semantic equivalence between
the original and the optimised program. This is planned future work.

## Implementation overview

The project is divided into several Agda modules, each of which is based on an optimisation stage of the compiler.
They each contain the respective Agda formalisation of the program transformation and a decision procedure which takes
two programs as input and decides whether the transformation is applicable. 

This module is at the top of the project hierarchy and contains the main decision procedure which verifies the entire optimisation
process. The final certification function receives a list of intermediate program ASTs produced by the compiler and outputs a file
containing the generated proof object, a.k.a. the _certificate_. The certificate can then be verified by third parties by loading
it into Agda and checking that it is correctly typed.

```
module VerifiedCompilation where
```

## Imports

```
import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Nullary using (_×-dec_)
import Relation.Binary using (Decidable)
open import Untyped
open import Utils as U using (Maybe;nothing;just;Either;inj₁;inj₂;List;[];_∷_;_×_;_,_)
open import RawU using (Untyped)
open import Data.String using (String;_++_)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤;tt)
import IO.Primitive as IO using (return;_>>=_)
import VerifiedCompilation.UCaseOfCase as UCC
import VerifiedCompilation.UForceDelay as UFD
open import Data.Empty using (⊥)
open import Scoped using (ScopeError;deBError)
open import VerifiedCompilation.Equality using (DecEq)
import Relation.Binary as Binary using (Decidable)
open import VerifiedCompilation.UntypedTranslation using (Translation; Relation; translation?)
import Relation.Binary as Binary using (Decidable)
import Relation.Unary as Unary using (Decidable)
open import Generics hiding (DecEq)
import Agda.Builtin.Sigma 
```

## Compiler optimisation traces

A `Trace` represents a sequence of optimisation transformations applied to a program. It is a list of pairs of ASTs,
where each pair represents the before and after of a transformation application.
The `IsTransformation` type is a sum type that represents the possible transformations which are implemented in their
respective modules. Adding a new transformation requires extending this type. 

The `isTrace?` decision procedure is at the core of the certification process. It produces the proof that the given
list of ASTs are in relation with one another according to the transformations implemented in the project. It is
parametrised by the relation type in order to provide a generic interface for testing, but in practice it is always
instantiated with the `IsTransformation` type.

The `IsTransformation?` decision procedure implements a logical disjunction of the different transformation types.

**TODO**: The `Trace` type or decision procedure should also enforce that the second element of a pair is the first
element of the next pair in the list. This might not be necessary if we decide that we can assume that the function
which produces a `Trace` always produces a correct one, although it might be useful to make this explicit in the type.

**TODO**: The compiler should provide information on which transformation was applied at each step in the trace.
`IsTransformation?` is currently quadratic in the number of transformations, which is not ideal. 

```

data Trace (R : Relation) : { X : Set } → List ((X ⊢) × (X ⊢)) → Set₁ where
  empty : {X : Set} → Trace R {X} []
  cons : {X : Set} {x x' : X ⊢} {xs : List ((X ⊢) × (X ⊢))} → R x x' → Trace R {X} xs → Trace R {X} ((x , x') ∷ xs)

data IsTransformation : Relation where
  isCoC : {X : Set} → (ast ast' : X ⊢) → UCC.CoC ast ast' → IsTransformation ast ast'
  isFD : {X : Set} → (ast ast' : X ⊢) → UFD.FD zero zero ast ast' → IsTransformation ast ast'

isTrace? : {X : Set} {R : Relation} → Binary.Decidable (R {X}) → Unary.Decidable (Trace R {X})
isTrace? {X} {R} isR? [] = yes empty
isTrace? {X} {R} isR? ((x₁ , x₂) ∷ xs) with isTrace? {X} {R} isR? xs
... | no ¬p = no λ {(cons a as) → ¬p as}
... | yes p with isR? x₁ x₂
...   | no ¬p = no λ {(cons x x₁) → ¬p x}
...   | yes p₁ = yes (cons p₁ p)
  
isTransformation? : {X : Set} {{_ : DecEq X}} → Binary.Decidable (IsTransformation {X})
isTransformation? ast₁ ast₂ with UCC.isCoC? ast₁ ast₂
... | scrt with UFD.isFD? zero zero ast₁ ast₂
isTransformation? ast₁ ast₂ | no ¬p | no ¬p₁ = no λ {(isCoC .ast₁ .ast₂ x) → ¬p x
                                                   ; (isFD .ast₁ .ast₂ x) → ¬p₁ x}
isTransformation? ast₁ ast₂ | no ¬p | yes p = yes (isFD ast₁ ast₂ p)
isTransformation? ast₁ ast₂ | yes p | no ¬p = yes (isCoC ast₁ ast₂ p)
-- TODO: this does not make much sense, see TODO above
isTransformation? ast₁ ast₂ | yes p | yes p₁ = yes (isCoC ast₁ ast₂ p)

```
## Serialising the proofs

The proof objects are converted to a textual representation which can be written to a file.

**TODO**: Finish the implementation. A textual representation is not usually ideal, but it is a good starting point.

```
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

showTrace : {X : Set} {xs : List ((X ⊢) × (X ⊢))} → Trace (Translation IsTransformation) xs → String
showTrace empty = "empty"
showTrace (cons x bla) = "(cons " ++ showTranslation x ++ showTrace bla ++ ")"

-- instance
--   traceD : HasDesc Trace
--   traceD = deriveDesc Trace
--   showMaybeBase : Show (Maybe ⊥)
--   showMaybeBase = record { show = λ {nothing → "nothing" }}
--   showMaybeInd : {X : Set} → {{Show X}} → Show (Maybe X)
--   showMaybeInd = record { show = λ {(just x) → "just " ++ show x
--                                     ; nothing → "nothing" }} 
--   decD : HasDesc Dec
--   decD = {!   !}
--   showTrace' = deriveShow traceD

serializeTraceProof : {X : Set} {xs : List ((X ⊢) × (X ⊢))} → Dec (Trace (Translation IsTransformation) xs) → String
serializeTraceProof (no ¬p) = "no" 
serializeTraceProof (yes p) = "yes " ++ showTrace p -- ++ show p

data Dec' (A : Set₁) : Set₁ where
  yes' : A → Dec' A
  no' : ¬ A → Dec' A

toDec' : {A : Set₁} → Dec A → Dec' A
toDec' (yes p) = yes' p
toDec' (no ¬p) = no' ¬p

mkPrintableProof : {xs : List ((Maybe ⊥ ⊢) × (Maybe ⊥ ⊢))} → Dec (Trace (Translation IsTransformation) xs) → Dec' (Trace (Translation IsTransformation) xs)
mkPrintableProof p = toDec' p 

-- printProof : {xs : List ((Maybe ⊥ ⊢) × (Maybe ⊥ ⊢))} → Dec (Trace (Translation IsTransformation) xs) → String
-- printProof {xs} p = {! show  !} (mkPrintableProof p) -- {Agda.Primitive.lsuc Agda.Primitive.lzero} {Dec' (Trace (Translation IsTransformation) xs)} (mkPrintableProof p)

```

## The certification function

The `runCertifier` function is the top-level function which can be called by the compiler through the foreign function interface.
It represents the "impure top layer" which receives the list of ASTs produced by the compiler and writes the certificate 
generated by the `certifier` function to disk. Again, the `certifier` is generic for testing purposes but it is instantiated
with the top-level decision procedures by the `runCertifier` function.

```

{-# FOREIGN GHC import qualified Data.Text.IO as TextIO #-}
{-# FOREIGN GHC import qualified System.IO as IO #-}
{-# FOREIGN GHC import qualified Data.Text as Text #-}

postulate FileHandle : Set
{-# COMPILE GHC FileHandle = type IO.Handle #-}

postulate
  writeFile : String → String → IO ⊤
  stderr : FileHandle
  hPutStrLn : FileHandle → String → IO ⊤

{-# COMPILE GHC writeFile = \f -> TextIO.writeFile (Text.unpack f) #-}
{-# COMPILE GHC stderr = IO.stderr #-}
{-# COMPILE GHC hPutStrLn = TextIO.hPutStr #-}

buildPairs : {X : Set} → List (Maybe X ⊢) -> List ((Maybe X ⊢) × (Maybe X ⊢))
buildPairs [] = []
buildPairs (x ∷ []) = (x , x) ∷ []
buildPairs (x₁ ∷ (x₂ ∷ xs)) = (x₁ , x₂) ∷ buildPairs (x₂ ∷ xs)

traverseEitherList : {A B E : Set} → (A → Either E B) → List A → Either E (List B) 
traverseEitherList _ [] = inj₂ []
traverseEitherList f (x ∷ xs) with f x
... | inj₁ err = inj₁ err
... | inj₂ x' with traverseEitherList f xs
...     | inj₁ err = inj₁ err
...     | inj₂ resList = inj₂ (x' ∷ resList)

certifier
  : {X : Set}
  → List Untyped
  → Unary.Decidable (Trace (Translation IsTransformation) {Maybe X})
  → Either ScopeError String
certifier {X} rawInput isRTrace? with traverseEitherList toWellScoped rawInput
... | inj₁ err = inj₁ err
... | inj₂ rawTrace = 
  let inputTrace = buildPairs rawTrace
   in inj₂ (serializeTraceProof (isRTrace? inputTrace))

runCertifier : String → List Untyped → IO ⊤
runCertifier fileName rawInput with certifier rawInput (isTrace? {Maybe ⊥} {Translation IsTransformation} (translation? isTransformation?))
... | inj₁ err = hPutStrLn stderr "error" -- TODO: pretty print error
... | inj₂ result = writeFile (fileName ++ ".agda") result
{-# COMPILE GHC runCertifier as runCertifier #-}
