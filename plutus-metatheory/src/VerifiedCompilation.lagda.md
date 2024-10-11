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
import VerifiedCompilation.UFloatDelay as UFlD
import VerifiedCompilation.UCSE as UCSE
open import Data.Empty using (⊥)
open import Scoped using (ScopeError;deBError)
open import VerifiedCompilation.Equality using (DecEq)
import Relation.Binary as Binary using (Decidable)
open import VerifiedCompilation.UntypedTranslation using (Translation; Relation; translation?)
import Relation.Binary as Binary using (Decidable)
import Relation.Unary as Unary using (Decidable)
import Agda.Builtin.Int
```

## Compiler optimisation traces

A `Trace` represents a sequence of optimisation transformations applied to a program. It is a list of pairs of ASTs
and a tag (`SimplifierTag`), where each pair represents the before and after of a transformation application and the
tag indicates which transformation was applied.
The `Transformation` type is a sum type that represents the possible transformations which are implemented in their
respective modules. 

The `isTrace?` decision procedure is at the core of the certification process. It produces the proof that the given
list of ASTs are in relation with one another according to the transformations implemented in the project.

The `isTransformation?` decision procedure just dispatches to the decision procedure indicated by the tag.

**TODO**: The `Trace` type or decision procedure should also enforce that the second element of a pair is the first
element of the next pair in the list. This might not be necessary if we decide that we can assume that the function
which produces a `Trace` always produces a correct one, although it might be useful to make this explicit in the type.
```

data SimplifierTag : Set where
  floatDelayT : SimplifierTag
  forceDelayT : SimplifierTag
  caseOfCaseT : SimplifierTag
  caseReduceT : SimplifierTag
  inlineT : SimplifierTag
  cseT : SimplifierTag

{-# FOREIGN GHC import UntypedPlutusCore.Transform.Simplifier #-}
{-# COMPILE GHC SimplifierTag = data SimplifierStage (FloatDelay | ForceDelay | CaseOfCase | CaseReduce | Inline | CSE) #-}

data Transformation : SimplifierTag → Relation where
  isCoC : {X : Set}{{_ : DecEq X}} → {ast ast' : X ⊢} → UCC.CaseOfCase ast ast' → Transformation caseOfCaseT ast ast'
  isFD : {X : Set}{{_ : DecEq X}} → {ast ast' : X ⊢} → UFD.ForceDelay ast ast' → Transformation forceDelayT ast ast'
  isFlD : {X : Set}{{_ : DecEq X}} → {ast ast' : X ⊢} → UFlD.FloatDelay ast ast' → Transformation floatDelayT ast ast'
  isCSE : {X : Set}{{_ : DecEq X}} → {ast ast' : X ⊢} → UCSE.UntypedCSE ast ast' → Transformation cseT ast ast'
  inlineNotImplemented : {X : Set}{{_ : DecEq X}} → {ast ast' : X ⊢} → Transformation inlineT ast ast'
  caseReduceNotImplemented : {X : Set}{{_ : DecEq X}} → {ast ast' : X ⊢} → Transformation caseReduceT ast ast'

data Trace : { X : Set } {{_ : DecEq X}} → List (SimplifierTag × (X ⊢) × (X ⊢)) → Set₁ where
  empty : {X : Set}{{_ : DecEq X}} → Trace {X} []
  cons
    : {X : Set}{{_ : DecEq X}} 
    {tag : SimplifierTag} {x x' : X ⊢}
    {xs : List (SimplifierTag × (X ⊢) × (X ⊢))}
    → Transformation tag x x'
    → Trace xs
    → Trace ((tag , x , x') ∷ xs)

isTransformation? : {X : Set} {{_ : DecEq X}} → (tag : SimplifierTag) → (ast ast' : X ⊢) → Nary.Decidable (Transformation tag ast ast')
isTransformation? tag ast ast' with tag
isTransformation? tag ast ast' | floatDelayT with UFlD.isFloatDelay? ast ast'
... | no ¬p = no λ { (isFlD x) → ¬p x }
... | yes p = yes (isFlD p)
isTransformation? tag ast ast' | forceDelayT with UFD.isForceDelay? ast ast'
... | no ¬p = no λ { (isFD x) → ¬p x }
... | yes p = yes (isFD p)
isTransformation? tag ast ast' | caseOfCaseT with UCC.isCaseOfCase? ast ast'
... | no ¬p = no λ { (isCoC x) → ¬p x }
... | yes p = yes (isCoC p)
isTransformation? tag ast ast' | caseReduceT = yes caseReduceNotImplemented
isTransformation? tag ast ast' | inlineT = yes inlineNotImplemented
isTransformation? tag ast ast' | cseT with UCSE.isUntypedCSE? ast ast'
... | no ¬p = no λ { (isCSE x) → ¬p x }
... | yes p = yes (isCSE p)

isTrace? : {X : Set} {{_ : DecEq X}} → Unary.Decidable (Trace {X})
isTrace? [] = yes empty
isTrace? ((tag , x₁ , x₂) ∷ xs) with isTrace? xs
... | no ¬pₜ = no λ {(cons _ rest) → ¬pₜ rest}
... | yes pₜ with isTransformation? tag x₁ x₂
...                 | no ¬pₑ = no λ {(cons x _) → ¬pₑ x}
...                 | yes pₑ = yes (cons pₑ pₜ)


```
## Serialising the proofs

The proof objects are converted to a textual representation which can be written to a file.

**TODO**: This is currently not supported. The `showTrace` function is a placeholder for the actual serialisation function.

```
showTrace : {X : Set} {{_ : DecEq X}} {xs : List (SimplifierTag × (X ⊢) × (X ⊢))} → Trace xs → String
showTrace _ = "TODO"

serializeTraceProof : {X : Set} {{_ : DecEq X}} {xs : List (SimplifierTag × (X ⊢) × (X ⊢))} → Dec (Trace xs) → String
serializeTraceProof (no ¬p) = "no"
serializeTraceProof (yes p) = "yes " ++ showTrace p

```

## The certification function

The `runCertifier` function is the top-level function which can be called by the compiler through the foreign function interface.
It represents the "impure top layer" which receives the list of ASTs produced by the compiler and writes the certificate
generated by the `certifier` function to disk. 

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

h : Agda.Builtin.Int.Int
h = Agda.Builtin.Int.pos 42

x : Either ? (⊥ ⊢) 
x = toWellScoped (RawU.UCon (RawU.tagCon RawU.integer h))

buildPairs : {X : Set} → List (Maybe X ⊢) -> List ((Maybe X ⊢) × (Maybe X ⊢))
buildPairs [] = []
buildPairs (x ∷ []) = (x , x) ∷ []
buildPairs (x₁ ∷ (x₂ ∷ xs)) = (x₁ , x₂) ∷ buildPairs (x₂ ∷ xs)

traverseEitherList : {A B E : Set} → (A → Either E B) → List A → Either E (List B)
traverseEitherList _ [] = inj₂ []
traverseEitherList f ((tag , before , after) ∷ xs) with f before
... | inj₁ e = inj₁ e
... | inj₂ b with f after
... | inj₁ e = inj₁ e
... | inj₂ a with traverseEitherList f xs
... | inj₁ e = inj₁ e
... | inj₂ xs' = inj₂ (((tag , b , a)) ∷ xs')

certifier
  : {X : Set} {{_ : DecEq X}}
  → List (SimplifierTag × Untyped × Untyped)
  → Either ScopeError String
certifier {X} rawInput with traverseEitherList (toWellScoped {X}) rawInput
... | inj₁ err = inj₁ err
... | inj₂ inputTrace = inj₂ (serializeTraceProof (isTrace? inputTrace))

runCertifier : String → List (SimplifierTag × Untyped × Untyped) → IO ⊤
runCertifier fileName rawInput with certifier {⊥} rawInput
... | inj₁ err = hPutStrLn stderr "error" -- TODO: pretty print error
... | inj₂ result = writeFile (fileName ++ ".agda") result
{-# COMPILE GHC runCertifier as runCertifier #-}
