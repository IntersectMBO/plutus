---
title: Compiler Traces
layout: page
---

A compiler trace is the structure that the compiler outputs and the certifier
operates on. It contains all the ASTs of the performed passes together with some
information about that pass.

```
module VerifiedCompilation.Trace where

open import RawU using (Untyped)
open import Data.List using (List ; _∷_ ; [])
open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Utils using (_×_ ; Maybe ; _,_)
open Maybe

```
## Pass tags
We enumerate the known passes and partition them into two categories:
- those which are not yet (fully) implemented in the certifier 
- those which are implemented in the certifier and we know they are correct.

```

data UncertifiedOptTag : Set where
  caseOfCaseT : UncertifiedOptTag
  letFloatOutT : UncertifiedOptTag

data CertifiedOptTag : Set where
  floatDelayT : CertifiedOptTag
  forceDelayT : CertifiedOptTag
  forceCaseDelayT : CertifiedOptTag
  caseReduceT : CertifiedOptTag
  inlineT : CertifiedOptTag
  cseT : CertifiedOptTag
  applyToCaseT : CertifiedOptTag

OptTag = Utils.Either UncertifiedOptTag CertifiedOptTag

FloatDelayT : OptTag
FloatDelayT = Utils.inj₂ floatDelayT
ForceDelayT : OptTag
ForceDelayT = Utils.inj₂ forceDelayT
ForceCaseDelayT : OptTag
ForceCaseDelayT = Utils.inj₂ forceCaseDelayT
CaseReduceT : OptTag
CaseReduceT = Utils.inj₂ caseReduceT
InlineT : OptTag
InlineT = Utils.inj₂ inlineT
CseT : OptTag
CseT = Utils.inj₂ cseT
ApplyToCaseT : OptTag
ApplyToCaseT = Utils.inj₂ applyToCaseT

CaseOfCaseT : OptTag
CaseOfCaseT = Utils.inj₁ caseOfCaseT
LetFloatOutT : OptTag
LetFloatOutT = Utils.inj₁ letFloatOutT

{-# COMPILE GHC CertifiedOptTag = data CertifiedOptStage (FloatDelay | ForceDelay | ForceCaseDelay | CaseReduce | Inline | CSE | ApplyToCase) #-}
{-# COMPILE GHC UncertifiedOptTag = data UncertifiedOptStage (CaseOfCase | LetFloatOut) #-}
```

## Hints
Some passes produce hints that help the certifier to perform a faster search.

```
data InlineHints : Set where
  var     : InlineHints
  expand  : InlineHints → InlineHints
  ƛ       : InlineHints → InlineHints
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
{-# COMPILE GHC InlineHints = data Hints.Inline (Hints.InlVar | Hints.InlExpand | Hints.InlLam | Hints.InlApply | Hints.InlDrop | Hints.InlForce | Hints.InlDelay | Hints.InlCon | Hints.InlBuiltin | Hints.InlError | Hints.InlConstr | Hints.InlCase) #-}
{-# COMPILE GHC Hints = data Hints.Hints (Hints.Inline | Hints.NoHints) #-}
```

## Compiler traces

A `Trace A` is a sequence of optimisation transformations applied to terms of
type `A`. Each transition is labeled with a `OptTag` that contains
information about which pass was performed.

```

data Trace (A : Set) : Set where
  -- One step in the pipeline, with its pass and input term
  step : OptTag → Hints → A → Trace A → Trace A
  -- Final AST in the trace
  done : A → Trace A

-- Get the first term in the trace
head : ∀{A} → Trace A → A
head (done x) = x
head (step _ _ x _) = x

```

`Dump` is the structure that is currently dumped on the Haskell side. We can convert it in a `Trace` using `toTrace`

```


-- The current trace structure dumped from Haskell
Dump : Set
Dump = List (OptTag × Hints × Untyped × Untyped)

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
    go : OptTag × Hints × Untyped × Untyped → Dump → Trace Untyped
    go (pass , hints , x , y) [] = step pass hints x (done y)
    go (pass , hints , x , y) ((pass' , hints' , _ , z) ∷ xs) = step pass hints x (go (pass' , hints' , y , z) xs)
```

`EvalResult` is used to report script execution costs, before and after an optimisation (or optimisations).

```
data EvalResult : Set where
  success : ℕ → ℕ → EvalResult
  failure : String → ℕ → ℕ → EvalResult

{-# FOREIGN GHC import FFI.CostInfo #-}
{-# COMPILE GHC EvalResult = data EvalResult (EvalSuccess | EvalFailure) #-}
```
