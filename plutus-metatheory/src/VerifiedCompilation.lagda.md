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

import Relation.Nullary using (_×-dec_)
import Relation.Binary using (Decidable)
open import Untyped
open import Utils as U using (Maybe;nothing;just;Either;inj₁;inj₂;List;[];_∷_;_×_;_,_)
open import RawU using (Untyped)
open import Data.String using (String;_++_)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤;tt)
import IO.Primitive.Core as IO using (return;_>>=_)
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
import Relation.Nary as Nary using (Decidable)
open import VerifiedCompilation.Certificate using (ProofOrCE; ce; proof; pcePointwise; MatchOrCE)

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

isTransformation? : {X : Set} {{_ : DecEq X}} → (tag : SimplifierTag) → MatchOrCE {X = X ⊢} (Transformation tag)
isTransformation? tag ast ast' with tag
isTransformation? tag ast ast' | floatDelayT with UFlD.isFloatDelay? ast ast'
... | ce b a = ce b a
... | proof p = proof (isFlD p)
isTransformation? tag ast ast' | forceDelayT with UFD.isForceDelay? ast ast'
... | ce b a = ce b a
... | proof p = proof (isFD p)
isTransformation? tag ast ast' | caseOfCaseT with UCC.isCaseOfCase? ast ast'
... | ce b a = ce b a
... | proof p = proof (isCoC p)
isTransformation? tag ast ast' | caseReduceT = proof caseReduceNotImplemented
isTransformation? tag ast ast' | inlineT = proof inlineNotImplemented
isTransformation? tag ast ast' | cseT with UCSE.isUntypedCSE? ast ast'
... | ce b a = ce b a
... | proof p = proof (isCSE p)

isTrace? : {X : Set} {{_ : DecEq X}} → (t : List (SimplifierTag × (X ⊢) × (X ⊢))) → ProofOrCE (Trace {X} t)
isTrace? [] = proof empty
isTrace? {X} ((tag , x₁ , x₂) ∷ xs) with isTrace? xs
... | ce b a = ce b a
... | proof pₜ with isTransformation? {X} tag x₁ x₂
...                 | ce b a = ce b a
...                 | proof pₑ = proof (cons pₑ pₜ)


```


## The certification function

The `runCertifier` function is the top-level function which can be called by the compiler.

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
  putStrLn : String → IO ⊤

{-# COMPILE GHC writeFile = \f -> TextIO.writeFile (Text.unpack f) #-}
{-# COMPILE GHC stderr = IO.stderr #-}
{-# COMPILE GHC hPutStrLn = TextIO.hPutStr #-}
{-# COMPILE GHC putStrLn = TextIO.putStrLn #-}

buildPairs : {X : Set} → List (Maybe X ⊢) -> List ((Maybe X ⊢) × (Maybe X ⊢))
buildPairs [] = []
buildPairs (x ∷ []) = (x , x) ∷ []
buildPairs (x₁ ∷ (x₂ ∷ xs)) = (x₁ , x₂) ∷ buildPairs (x₂ ∷ xs)

traverseEitherList : {A B E : Set} → (A → Either E B) → List (SimplifierTag × A × A) → Either E (List (SimplifierTag × B × B))
traverseEitherList _ [] = inj₂ []
traverseEitherList f ((tag , before , after) ∷ xs) with f before
... | inj₁ e = inj₁ e
... | inj₂ b with f after
... | inj₁ e = inj₁ e
... | inj₂ a with traverseEitherList f xs
... | inj₁ e = inj₁ e
... | inj₂ xs' = inj₂ (((tag , b , a)) ∷ xs')

data Cert : Set₂ where
  cert
    : {X : Set} {result : List (SimplifierTag × (X ⊢) × (X ⊢))} {{_ : DecEq X}}
    → ProofOrCE(Trace {X} result)
    → Cert

runCertifier : (t : List (SimplifierTag × Untyped × Untyped)) → Maybe Cert
runCertifier rawInput with traverseEitherList (toWellScoped {⊥}) rawInput
... | inj₁ _ = nothing
... | inj₂ inputTrace = just (cert (isTrace? inputTrace))

open import Data.Bool.Base using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

passed? : Maybe Cert → Bool
passed? (just (cert (ce _ _))) = false
passed? (just (cert (proof _))) = true
passed? nothing = false

runCertifierMain : List (SimplifierTag × Untyped × Untyped) → IO ⊤
runCertifierMain asts with runCertifier asts
... | just (cert (proof a)) =
  putStrLn "The compilation was successfully certified."
... | just (cert (ce b a)) =
  putStrLn "The compilation was not successfully certified. Please open a bug report at https://www.github.com/IntersectMBO/plutus and attach the faulty certificate."
... | nothing =
  putStrLn "The certifier was unable to check the compilation. Please open a bug report at https://www.github.com/IntersectMBO/plutus."
{-# COMPILE GHC runCertifierMain as runCertifierMain #-}
