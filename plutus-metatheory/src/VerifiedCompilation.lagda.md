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

This module is at the top of the project hierarchy and contains the main decision procedure which certified the entire optimisation
process. The final certification function receives a list of intermediate program ASTs produced by the compiler and outputs a file
containing the generated proof object, a.k.a. the _certificate_. The certificate can then be checked by third parties by loading
it into Agda and checking that it is correctly typed.

```
module VerifiedCompilation where
```

## Imports

```
open import Function using (_∘_)
open import Data.Bool.Base using (Bool; false; true)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

open import Untyped
open import Utils
open import RawU using (Untyped)
import VerifiedCompilation.UCaseOfCase as UCC
import VerifiedCompilation.UForceDelay as UFD
import VerifiedCompilation.UFloatDelay as UFlD
import VerifiedCompilation.UCSE as UCSE
import VerifiedCompilation.UInline as UInline
import VerifiedCompilation.UCaseReduce as UCR
open import VerifiedCompilation.NotImplemented
open import VerifiedCompilation.Trace
open import VerifiedCompilation.Certificate

-- | The failure modes we expose to Haskell
data Error : Set where
  emptyDump : Error
  illScoped : Error
  counterExample : Error
  abort : Error
```

## Translation Relations and Certifiers

We map a `SimplifierTag` to the corresponding translation relation and certifier (decision procedure/checker).

```

RelationOf : SimplifierTag → (0 ⊢ → 0 ⊢ → Set)
RelationOf floatDelayT = UFlD.FloatDelay
RelationOf forceDelayT = UFD.ForceDelay
RelationOf caseOfCaseT = UCC.CaseOfCase
RelationOf caseReduceT = UCR.UCaseReduce
RelationOf cseT = UCSE.UntypedCSE
RelationOf forceCaseDelayT = NotImplemented accept -- FIXME: https://github.com/IntersectMBO/plutus-private/issues/2053
RelationOf inlineT = NotImplemented accept -- FIXME: https://github.com/IntersectMBO/plutus-private/issues/1475

certify : (pass : SimplifierTag) → Certifier (RelationOf pass)
certify floatDelayT = UFlD.certFloatDelay
certify forceDelayT = UFD.certForceDelay
certify caseOfCaseT = UCC.certCaseOfCase
certify caseReduceT = UCR.certCaseReduce
certify cseT = UCSE.certCSE
certify forceCaseDelayT = certNotImplemented
certify inlineT = certNotImplemented

```

A `Certificate t` expresses the main theorem of a certificate t: a sequence
(product) of translation relations, instantiated to their corresponding terms in
the trace. `certifyᵗ` then attempts to certify this property by running the
corresponding certifiers of each pass.

```

Certificate : Trace (0 ⊢) → Set
Certificate (done x) = ⊤
Certificate (step pass t ts) = RelationOf pass t (head ts) × Certificate ts

certifyᵗ : (trace : Trace (0 ⊢)) → Either Error (Certificate trace)
certifyᵗ (done x) = inj₂ tt
certifyᵗ (step pass x xs) with certify pass x (head xs)
... | ce _ _ _ _ = inj₁ counterExample
... | abort _ _ _ = inj₁ abort
... | proof p = do
  ps ← certifyᵗ xs
  return (p , ps)

```

## Scope Checking

Translation relations are defined for scoped terms only, so we need to scope
check all terms in the trace.

```

checkScope : Untyped → Maybe (0 ⊢)
checkScope = eitherToMaybe ∘ scopeCheckU0

-- Scope-check all terms in a trace
checkScopeᵗ : Trace Untyped → Maybe (Trace (0 ⊢))
checkScopeᵗ (done x) = do
  x' ← checkScope x
  return (done x')
checkScopeᵗ (step pass t ts) = do
  t' ← checkScope t
  ts' ← checkScopeᵗ ts
  return (step pass t' ts')

```

## Running the certifier

```
run : (d : Dump) → Either Error (Σ (Trace (0 ⊢)) Certificate)
run dump = do
  trace ← try (toTrace dump) emptyDump
  trace' ← try (checkScopeᵗ trace) illScoped
  cert ← certifyᵗ trace'
  return (trace' , cert)

```

To run the certifier from Haskell (as done in the compiler)

```
open import Data.String using (String)
open import Agda.Builtin.IO using (IO)

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

-- FIXME: Instead of `Maybe Bool`, we should use something like on the Haskell side
runCertifierMain : Dump → Maybe Bool
runCertifierMain dump with run dump
... | inj₂ (trace , p)    = just true
... | inj₁ counterExample = just false
... | inj₁ abort          = just false
... | inj₁ illScoped      = nothing
... | inj₁ emptyDump      = nothing
{-# COMPILE GHC runCertifierMain as runCertifierMain #-}
```
