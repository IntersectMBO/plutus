---
title: Compiler Traces
layout: page
---

A compiler trace is the structure that the compiler outputs and the certifier
operates on. It contains all the ASTs of the performed passes together with some
information about that pass.

```
{-# OPTIONS --allow-unsolved-metas #-}
module VerifiedCompilation.Trace where

open import RawU using (Untyped)
open import Data.List using (List ; _∷_ ; [])
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Utils using (_×_ ; Maybe ; _,_)
open Maybe

```
## Pass tags
We enumerate the known passes:

```

data Certified : Set where
  certified : Certified

data NotCertified : Set where
  notCertified : NotCertified

data SimplifierTag : Set → Set where
  floatDelayT : SimplifierTag Certified
  forceDelayT : SimplifierTag Certified
  forceCaseDelayT : SimplifierTag Certified
  caseOfCaseT : SimplifierTag NotCertified
  caseReduceT : SimplifierTag Certified
  inlineT : SimplifierTag Certified
  cseT : SimplifierTag Certified
  applyToCaseT : SimplifierTag Certified
  unknown : SimplifierTag NotCertified -- a placeholder for passes that we don't yet know of, so the certifier doesn't break if a pass was added

{-# FOREIGN GHC import UntypedPlutusCore.Transform.Simplifier #-}
{-# FOREIGN GHC {-# LANGUAGE GADTs #-} #-}
{-# COMPILE GHC SimplifierTag = data SimplifierStage (FloatDelay | ForceDelay | ForceCaseDelay | CaseOfCase | CaseReduce | Inline | CSE | ApplyToCase | Unknown) #-}

isCertified? : {isCertified : Set} → SimplifierTag isCertified → isCertified
isCertified? floatDelayT = certified
isCertified? forceDelayT = certified
isCertified? forceCaseDelayT = certified
isCertified? caseOfCaseT = notCertified
isCertified? caseReduceT = certified
isCertified? inlineT = certified
isCertified? cseT = certified
isCertified? applyToCaseT = certified
isCertified? unknown = notCertified

```

## Hints
Some passes produce hints that help the certifier to perform a faster search.

```
data InlineHints : Set where
  var     : InlineHints
  expand  : InlineHints → InlineHints
  ƛ       : InlineHints → InlineHints
  ƛ↓      : InlineHints → InlineHints
  _·_     : InlineHints → InlineHints → InlineHints
  _·↓     : InlineHints → InlineHints
  force   : InlineHints → InlineHints
  delay   : InlineHints → InlineHints
  con     : InlineHints
  builtin : InlineHints
  error   : InlineHints
  constr  : List InlineHints → InlineHints
  case    : InlineHints → List InlineHints → InlineHints

data Hints : Set where
  inline : InlineHints → Hints
  none : Hints

{-# FOREIGN GHC import UntypedPlutusCore.Transform.Certify.Trace #-}
{-# FOREIGN GHC import qualified UntypedPlutusCore.Transform.Certify.Hints as Hints #-}
{-# COMPILE GHC InlineHints = data Hints.Inline (Hints.InlVar | Hints.InlExpand | Hints.InlLam | Hints.InlLamDrop | Hints.InlApply | Hints.InlDrop | Hints.InlForce | Hints.InlDelay | Hints.InlCon | Hints.InlBuiltin | Hints.InlError | Hints.InlConstr | Hints.InlCase) #-}
{-# COMPILE GHC Hints = data Hints.Hints (Hints.Inline | Hints.NoHints) #-}
```

## Compiler traces

A `Trace A` is a sequence of optimisation transformations applied to terms of
type `A`. Each transition is labeled with a `SimplifierTag` that contains
information about which pass was performed.

```

-- record Step (A : Set) : Set₁ where
--   constructor certifierStep
--   field
--     isCertified : Set
--     tag : SimplifierTag isCertified
--     hints : Hints
--     inputTerm : A

data Step (A : Set) : Set where
  implementedStep : SimplifierTag Certified → Hints → A → Step A
  notImplementedStep : SimplifierTag NotCertified → Hints → A → Step A

data Trace (A : Set) : Set₁ where
  -- One step in the pipeline, with its pass and input term
  step : Step A → Trace A → Trace A 
  -- Final AST in the trace
  done : A → Trace A

-- Get the first term in the trace
head : ∀{A} → Trace A → A
head (done term) = term
head (step (implementedStep _ _ x) _) = x
head (step (notImplementedStep _ _ x) _) = x

```

`Dump` is the structure that is currently dumped on the Haskell side. We can convert it in a `Trace` using `toTrace`

```

record DumpStep : Set₁ where
  constructor dumpStep
  field
    isCertified : Set
    tag : SimplifierTag isCertified
    hints : Hints
    inputTerm : Untyped
    outputTerm : Untyped

-- The current trace structure dumped from Haskell
Dump = List DumpStep

--
-- Since there is duplication in the dump, i.e. it is of the form
--
--     [(_ , x , y) ; (_ , y , z) ; (_ , z , w) ...]
--
-- This conversion entirely ignores the duplicated terms.
-- FIXME: just dump the Trace structure directly from
-- Haskell, this function won't be necessary
toTrace : Dump → Maybe (Trace Untyped)
toTrace [] = nothing
toTrace (x ∷ xs) = just (go x xs)
  where
    go : DumpStep → Dump → Trace Untyped
    go bl fl = {!   !}
    -- go (dumpStep _ floatDelayT hints x y) [] with isCertified? floatDelayT
    -- ... | certified = {! UFlD.FloatDelay  !}
    -- go (dumpStep _ forceDelayT hints x y) [] = {!   !}
    -- go (dumpStep _ forceCaseDelayT hints x y) [] = {!   !}
    -- go (dumpStep _ caseOfCaseT hints x y) [] = {!   !}
    -- go (dumpStep _ caseReduceT hints x y) [] = {!   !}
    -- go (dumpStep _ inlineT hints x y) [] = {!   !}
    -- go (dumpStep _ cseT hints x y) [] = {!   !}
    -- go (dumpStep _ applyToCaseT hints x y) [] = {!   !}
    -- go (dumpStep _ unknown hints x y) [] = {!   !} -- with isCertified? pass
    -- ... | certified =
    --         step (implementedStep pass hints x) (done y)
    -- ... | notCertified =
    --         step (notImplementedStep pass hints x) (done y)
    -- go (dumpStep ty pass hints x y) ((dumpStep ty' pass' hints' _  z) ∷ xs) =
    --   step (certifierStep ty pass hints x) (go (dumpStep ty' pass' hints' y z) xs)
```

`EvalResult` is used to report script execution costs, before and after an optimisation (or optimisations).

```
data EvalResult : Set where
  success : ℕ → ℕ → EvalResult
  failure : String → ℕ → ℕ → EvalResult

{-# FOREIGN GHC import FFI.CostInfo #-}
{-# COMPILE GHC EvalResult = data EvalResult (EvalSuccess | EvalFailure) #-}
```
