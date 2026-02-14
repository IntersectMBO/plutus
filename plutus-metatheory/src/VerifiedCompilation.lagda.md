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
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Untyped
open import Utils as U using (Maybe;nothing;just;Either;inj₁;inj₂;List;[];_∷_;_×_;_,_)
open import RawU using (Untyped)
open import Data.String using (String)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
import VerifiedCompilation.UCaseOfCase as UCC
import VerifiedCompilation.UForceDelay as UFD
import VerifiedCompilation.UFloatDelay as UFlD
import VerifiedCompilation.UCSE as UCSE
import VerifiedCompilation.UInline as UInline
import VerifiedCompilation.UCaseReduce as UCR
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)
open import Data.Empty using (⊥)
open import Untyped.Equality using (DecEq)
open import Untyped.RenamingSubstitution using (Sub)
open import VerifiedCompilation.UntypedTranslation using (Relation)
import Relation.Unary as Unary using (Decidable)
import Agda.Builtin.Int
import Relation.Nary as Nary using (Decidable)
open import VerifiedCompilation.Certificate using (CertResult; Hints; inline; none; ce; proof; abort; pcePointwise; MatchOrCE; SimplifierTag)
open import Agda.Builtin.Sigma using (Σ; _,_)
```

## Compiler optimisation traces

A `Trace` represents a sequence of optimisation transformations applied to a program. It is a list of pairs of ASTs
and a tag (`SimplifierTag`), where each pair represents the before and after of a transformation application and the
tag indicates which transformation was applied.
The `Transformation` type is a sum type that represents the possible transformations which are implemented in their
respective modules.

The `isTrace?` decision procedure is at the core of the certification process. It produces the proof that the given
list of ASTs are in relation with one another according to the transformations implemented in the project.

The `isTransformation?` procedure just dispatches to the decision or checking procedure indicated by the tag.

**TODO**: The `Trace` type or decision procedure should also enforce that the second element of a pair is the first
element of the next pair in the list. This might not be necessary if we decide that we can assume that the function
which produces a `Trace` always produces a correct one, although it might be useful to make this explicit in the type.
```

data Transformation : SimplifierTag → Relation where
  isCoC : {X : ℕ} → {ast ast' : X ⊢} → UCC.CaseOfCase ast ast' → Transformation SimplifierTag.caseOfCaseT ast ast'
  isFD : {X : ℕ} → {ast ast' : X ⊢} → UFD.ForceDelay ast ast' → Transformation SimplifierTag.forceDelayT ast ast'
  isFlD : {X : ℕ} → {ast ast' : X ⊢} → UFlD.FloatDelay ast ast' → Transformation SimplifierTag.floatDelayT ast ast'
  isCSE : {X : ℕ} → {ast ast' : X ⊢} → UCSE.UntypedCSE ast ast' → Transformation SimplifierTag.cseT ast ast'
  isInline : {ast ast' : 0 ⊢} → UInline.Inline (λ()) UInline.□ ast ast' → Transformation SimplifierTag.inlineT ast ast'
  isCaseReduce : {X : ℕ} → {ast ast' : X ⊢} → UCR.UCaseReduce ast ast' → Transformation SimplifierTag.caseReduceT ast ast'
  backdoor : {X : ℕ} → {tag : SimplifierTag} → {ast ast' : X ⊢} → Transformation tag ast ast'
  forceCaseDelayNotImplemented : {X : ℕ} → {ast ast' : X ⊢} → Transformation SimplifierTag.forceCaseDelayT ast ast'

data Trace : { X : ℕ }  → List (SimplifierTag × Hints × (X ⊢) × (X ⊢)) → Set where
  empty : {X : ℕ} → Trace {X} []
  cons
    : {X : ℕ}
    {tag : SimplifierTag} {hints : Hints} {x x' : X ⊢}
    {xs : List (SimplifierTag × Hints × (X ⊢) × (X ⊢))}
    → Transformation tag x x'
    → Trace xs
    → Trace ((tag , hints , x , x') ∷ xs)

isTransformation? : {X : ℕ}  → (tag : SimplifierTag) → (hints : Hints) → (a : X ⊢) → (b : X ⊢) → CertResult (Transformation tag a b)
isTransformation? tag hints ast ast' with tag
isTransformation? tag hints ast ast' | SimplifierTag.floatDelayT = proof backdoor
isTransformation? tag hints ast ast' | SimplifierTag.forceDelayT = proof backdoor
isTransformation? tag hints ast ast' | SimplifierTag.forceCaseDelayT = proof forceCaseDelayNotImplemented
isTransformation? tag hints ast ast' | SimplifierTag.caseOfCaseT = proof backdoor
isTransformation? tag hints ast ast' | SimplifierTag.caseReduceT = proof backdoor
isTransformation? {X} tag hints ast ast' | SimplifierTag.inlineT with hints | X
... | inline h | 0 with UInline.top-check h ast ast'
...                     | proof p = proof (isInline p)
...                     | abort t b a = abort t b a
isTransformation? tag hints ast ast' | SimplifierTag.inlineT
    | _ | _ = abort tag ast ast'
isTransformation? tag hints ast ast' | SimplifierTag.cseT = proof backdoor

isTrace? : {X : ℕ}  → (t : List (SimplifierTag × Hints × (X ⊢) × (X ⊢))) → CertResult (Trace {X} t)
isTrace? [] = proof empty
isTrace? {X} ((tag , hints , x₁ , x₂) ∷ xs) with isTrace? xs
... | ce ¬p t b a = ce (λ { (cons x xx) → ¬p xx}) t b a
... | abort t b a = abort t b a
... | proof pₜ with isTransformation? {X} tag hints x₁ x₂
...                 | ce ¬p t b a = ce (λ { (cons x xx) → ¬p x}) t b a
...                 | abort t b a = abort t b a
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

buildPairs : {X : ℕ} → List (suc X ⊢) -> List ((suc X ⊢) × (suc X ⊢))
buildPairs [] = []
buildPairs (x ∷ []) = (x , x) ∷ []
buildPairs (x₁ ∷ (x₂ ∷ xs)) = (x₁ , x₂) ∷ buildPairs (x₂ ∷ xs)

traverseEitherList : {A B E : Set} → (A → Either E B) → List (SimplifierTag × Hints × A × A) → Either E (List (SimplifierTag × Hints × B × B))
traverseEitherList _ [] = inj₂ []
traverseEitherList f ((tag , hints , before , after) ∷ xs) with f before
... | inj₁ e = inj₁ e
... | inj₂ b with f after
... | inj₁ e = inj₁ e
... | inj₂ a with traverseEitherList f xs
... | inj₁ e = inj₁ e
... | inj₂ xs' = inj₂ (((tag , hints , b , a)) ∷ xs')

data Cert : Set₂ where
  cert
    : {X : ℕ} {result : List (SimplifierTag × Hints × (X ⊢) × (X ⊢))}
    → CertResult (Trace {X} result)
    → Cert

runCertifier : List (SimplifierTag × Hints × Untyped × Untyped) → Maybe Cert
runCertifier rawInput with traverseEitherList scopeCheckU0 rawInput
... | inj₁ _ = nothing
... | inj₂ inputTrace = just (cert (isTrace? inputTrace))

getCE : {A B : Set} → Maybe Cert → Maybe (Σ _ \A → (Σ _ \B → (SimplifierTag × A × B)))
getCE nothing = nothing
getCE (just (cert (proof _))) = nothing
getCE (just (cert (abort _ _ _))) = nothing
getCE (just (cert (ce _ {X} {X'} t b a))) = just (X , X' , t , b , a)

open import Data.Bool.Base using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

passed? : Maybe Cert → Bool
passed? (just (cert (ce _ _ _ _))) = false
passed? (just (cert (abort _ _ _))) = false
passed? (just (cert (proof _))) = true
passed? nothing = false

runCertifierMain : List (SimplifierTag × Hints × Untyped × Untyped) → Maybe Bool
runCertifierMain asts with runCertifier asts
... | just (cert (proof a)) = just true
... | just (cert (ce ¬p t b a)) = just false
... | just (cert (abort _ _ _)) = just false
... | nothing = nothing
{-# COMPILE GHC runCertifierMain as runCertifierMain #-}
