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
{-# OPTIONS --allow-unsolved-metas #-}
module VerifiedCompilation where
```

## Imports

```
import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
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
import Relation.Nary as Nary using (Decidable)

data SimplifierTag : Set where
  floatDelayT : SimplifierTag
  forceDelayT : SimplifierTag
  caseOfCaseT : SimplifierTag
  caseReduceT : SimplifierTag
  inlineT : SimplifierTag
  cseT : SimplifierTag

{-# COMPILE GHC SimplifierTag = data UPLCSimplifierStage (FloatDelay | ForceDelay | CaseOfCase | CaseReduce | Inline | CSE) #-}

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
TaggedRelation = { X : Set } → {{_ : DecEq X}} → SimplifierTag → (X ⊢) → (X ⊢) → Set₁

data Trace (R : TaggedRelation) : { X : Set } {{_ : DecEq X}} → List (SimplifierTag × (X ⊢) × (X ⊢)) → Set₁ where
  empty : {X : Set}{{_ : DecEq X}}  → Trace R {X} []
  cons : {X : Set}{{_ : DecEq X}}  {tag : SimplifierTag} {x x' : X ⊢} {xs : List (SimplifierTag × (X ⊢) × (X ⊢))} → R tag x x' → Trace R {X} xs → Trace R {X} ((tag , x , x') ∷ xs)

data IsTransformation : Relation where
  isCoC : {X : Set}{{_ : DecEq X}} → (tag : SimplifierTag) → (ast ast' : X ⊢) → UCC.CoC ast ast' → IsTransformation ast ast'
  isFD : {X : Set}{{_ : DecEq X}} → (tag : SimplifierTag) → (ast ast' : X ⊢) → UFD.FD zero zero ast ast' → IsTransformation ast ast'

isTrace? : {X : Set} {{_ : DecEq X}} {R : TaggedRelation} → Nary.Decidable (R {X}) → Unary.Decidable (Trace R {X})
isTrace? {X} {R = R} isR? [] = yes empty
isTrace? {X} {R = R} isR? ((tag , x₁ , x₂) ∷ xs) with isTrace? {X} {R = R} isR? xs
... | no ¬pₜ = no λ {(cons _ rest) → ¬pₜ rest}
... | yes pₜ with isR? tag x₁ x₂
... | no ¬pₑ = no λ {(cons x _) → ¬pₑ x}
... | yes pₑ = yes (cons pₑ pₜ)

isTransformation? : {X : Set} {{_ : DecEq X}} → Nary.Decidable (IsTransformation {X})
isTransformation? ast₁ ast₂ = {!   !}

```
## Serialising the proofs

The proof objects are converted to a textual representation which can be written to a file.

**TODO**: Finish the implementation. A textual representation is not usually ideal, but it is a good starting point.

```
-- showTranslation : {X : Set} {{_ : DecEq X}} {ast ast' : X ⊢} → Translation IsTransformation ast ast' → String
-- showTranslation (Translation.istranslation x) = "istranslation TODO"
-- showTranslation Translation.var = "var"
-- showTranslation (Translation.ƛ t) = "(ƛ " ++ showTranslation t ++ ")"
-- showTranslation (Translation.app t t₁) = "(app " ++ showTranslation t ++ " " ++ showTranslation t₁ ++ ")"
-- showTranslation (Translation.force t) = "(force " ++ showTranslation t ++ ")"
-- showTranslation (Translation.delay t) = "(delay " ++ showTranslation t ++ ")"
-- showTranslation Translation.con = "con"
-- showTranslation (Translation.constr x) = "(constr TODO)"
-- showTranslation (Translation.case x t) = "(case TODO " ++ showTranslation t ++ ")"
-- showTranslation Translation.builtin = "builtin"
-- showTranslation Translation.error = "error"
-- 
-- showTrace : {X : Set} {{_ : DecEq X}} {xs : List (SimplifierTag × (X ⊢) × (X ⊢))} → Trace (Translation IsTransformation) xs → String
-- showTrace empty = "empty"
-- showTrace (cons x bla) = "(cons " ++ showTranslation x ++ showTrace bla ++ ")"

-- serializeTraceProof : {X : Set} {{_ : DecEq X}} {xs : List (SimplifierTag × (X ⊢) × (X ⊢))} → Dec (Trace (Translation IsTransformation) xs) → String
-- serializeTraceProof (no ¬p) = "no"
-- serializeTraceProof (yes p) = "yes " ++ showTrace p

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
{-# FOREIGN GHC import PlutusCore.Compiler.Types #-}

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

traverseEitherList : {A B E : Set} → (A → Either E B) → List (SimplifierTag × A × A) → Either E (List (SimplifierTag × B × B))
traverseEitherList _ [] = inj₂ []
traverseEitherList f ((tag , before , after) ∷ xs) = {!   !}

certifier
  : {X : Set} {{_ : DecEq X}}
  → List (SimplifierTag × Untyped × Untyped)
  → Unary.Decidable (Trace (Translation IsTransformation) {Maybe X})
  → Either ScopeError String
certifier {X} rawInput isRTrace? with traverseEitherList toWellScoped rawInput
... | inj₁ err = inj₁ err
... | inj₂ inputTrace = inj₂ ? -- (serializeTraceProof (isRTrace? inputTrace))

runCertifier : String → List (SimplifierTag × Untyped × Untyped) → IO ⊤
runCertifier fileName rawInput with certifier rawInput (isTrace? {Maybe ⊥} {Translation IsTransformation} (translation? isTransformation?))
... | inj₁ err = hPutStrLn stderr "error" -- TODO: pretty print error
... | inj₂ result = writeFile (fileName ++ ".agda") result
{-# COMPILE GHC runCertifier as runCertifier #-}
