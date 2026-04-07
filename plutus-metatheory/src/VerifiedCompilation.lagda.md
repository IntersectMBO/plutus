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

This module is at the top of the project hierarchy and contains the main functions that certify the UPLC optimisation
process. The final certification function receives a list of intermediate program ASTs produced by the compiler and outputs a file
containing the generated proof object, a.k.a. the _certificate_. The certificate can then be checked by third parties by loading
it into Agda and checking that it is correctly typed.

```
module VerifiedCompilation where
```

## Imports

```
open import Function using (_∘_)
open import Data.Bool.Base
open import Data.Maybe using (is-just ; fromMaybe)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

open import Untyped
open import Utils
open import RawU using (Untyped)
import VerifiedCompilation.UApplyToCase as UA2C
import VerifiedCompilation.UCaseOfCase as UCC
import VerifiedCompilation.UForceDelay as UFD
import VerifiedCompilation.UFloatDelay as UFlD
import VerifiedCompilation.UForceCaseDelay as UFCD
import VerifiedCompilation.UCSE as UCSE
import VerifiedCompilation.UInline as UInline
import VerifiedCompilation.UCaseReduce as UCR
open import VerifiedCompilation.NotImplemented
open import VerifiedCompilation.Trace
open import VerifiedCompilation.Certificate hiding (_>>=_)


-- | The failure modes of the certifier
data Error : Set where
  emptyDump : Error
  illScoped : Error
  counterExample : SimplifierTag → Error
  abort : SimplifierTag → Error
```

## Translation Relations and Certifiers

We map a `SimplifierTag` to the corresponding translation relation, or `nothing`
if we don't have a translation relation.

```
mRelationOf : SimplifierTag → Maybe (0 ⊢ → 0 ⊢ → Set)
mRelationOf floatDelayT     = just UFlD.FloatDelay
mRelationOf forceDelayT     = just UFD.ForceDelay
mRelationOf caseReduceT     = just UCR.UCaseReduce
mRelationOf cseT            = just UCSE.UntypedCSE
mRelationOf inlineT         = just (UInline.Inline (λ()) UInline.□)
mRelationOf unknown         = nothing
mRelationOf caseOfCaseT     = nothing -- FIXME: https://github.com/IntersectMBO/plutus-private/issues/2054
mRelationOf forceCaseDelayT = just UFCD.ForceCaseDelay
mRelationOf applyToCaseT    = just UA2C.UApplyToCase
mRelationOf letFloatOutT    = nothing
```

We default to the `NotImplemented` relation to give each `SimplifierTag` a relation:

```
RelationOf : SimplifierTag → (0 ⊢ → 0 ⊢ → Set)
RelationOf = fromMaybe (NotImplemented accept) ∘ mRelationOf

hasRelation : SimplifierTag → Bool
hasRelation = is-just ∘ mRelationOf
```

The corresponding certifier can then be called for a given pass:

```
certifyPass : (pass : SimplifierTag) → Hints → (M M' : 0 ⊢) → CertResult (RelationOf pass M M')
certifyPass floatDelayT _       = decider UFlD.isFloatDelay?
certifyPass forceDelayT _       = decider UFD.isForceDelay?
certifyPass caseReduceT _       = decider UCR.isCaseReduce?
certifyPass cseT _              = decider UCSE.isUntypedCSE?
certifyPass caseOfCaseT _       = certNotImplemented
certifyPass forceCaseDelayT _   = decider UFCD.isForceCaseDelay?
certifyPass applyToCaseT _      = decider UA2C.a2c?ᶜᶜ
certifyPass inlineT (inline hs) = checker (UInline.top-check hs)
certifyPass inlineT none        = λ M M' → abort inlineT M M'
certifyPass letFloatOutT _      = certNotImplemented
certifyPass unknown _           = certNotImplemented
```

A `Certificate t` states the main theorem of a trace `t`: a sequence (product)
of translation relations, instantiated to their corresponding terms from the
trace. `certify` then attempts to certify this property by running the
corresponding certifiers of each pass.

```
Certificate : Trace (0 ⊢) → Set
Certificate (done _) = ⊤
Certificate (step pass hints t ts) = RelationOf pass t (head ts) × Certificate ts

certify : (trace : Trace (0 ⊢)) → Either Error (Certificate trace)
certify (done _) = inj₂ tt
certify (step pass hints x xs) with certifyPass pass hints x (head xs)
... | ce _ tag _ _ = inj₁ (counterExample tag)
... | abort tag _ _ = inj₁ (abort tag)
... | proof p =
  do
    ps ← certify xs
    return (p , ps)
```

If the certifier succeeds, we can produce the certificate:

```
cert : (trace : Trace (0 ⊢)) → (e : Either Error (Certificate trace)) → T (is-inj₂ e) → Certificate trace
cert _ (inj₂ cert) tt = cert
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
checkScopeᵗ (step pass hints t ts) = do
  t' ← checkScope t
  ts' ← checkScopeᵗ ts
  return (step pass hints t' ts')
```
