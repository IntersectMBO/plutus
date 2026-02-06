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
open import Utils

```
## Pass tags

We enumerate the known passes:

```

data SimplifierTag : Set where
  floatDelayT : SimplifierTag
  forceDelayT : SimplifierTag
  forceCaseDelayT : SimplifierTag
  caseOfCaseT : SimplifierTag
  caseReduceT : SimplifierTag
  inlineT : SimplifierTag
  cseT : SimplifierTag

{-# FOREIGN GHC import UntypedPlutusCore.Transform.Simplifier #-}
{-# COMPILE GHC SimplifierTag = data SimplifierStage (FloatDelay | ForceDelay | ForceCaseDelay | CaseOfCase | CaseReduce | Inline | CSE) #-}

```

## Compiler traces

A `Trace A` is a sequence of optimisation transformations applied to terms of
type `A`. Each transition is labeled with a `SimplifierTag` that contains
information about which pass was performed.

```

data Trace (A : Set) : Set where
  -- One step in the pipeline, with its pass and input term
  step : SimplifierTag → A → Trace A → Trace A
  -- Final AST in the trace
  done : A → Trace A

-- Get the first term in the trace
head : ∀{A} → Trace A → A
head (done x) = x
head (step _ x _) = x

```

`Dump` is the structure that is currently dumped on the Haskell side. We can convert it in a `Trace` using `toTrace`

```

-- FIXME: remove the Dump type and dump the Trace structure directly from
-- Haskell

-- The current trace structure dumped from Haskell
Dump : Set
Dump = List (SimplifierTag × Untyped × Untyped)

-- Since there is duplication in the dump, i.e. it is of the form
--
--     [(_ , x , y) ; (_ , y , z) ; (_ , z , w) ...]
--
-- This conversion entirely ignores the duplicated terms.
toTrace : Dump → Maybe (Trace Untyped)
toTrace [] = nothing
toTrace (x ∷ xs) = just (go x xs)
  where
    go : SimplifierTag × Untyped × Untyped → Dump → Trace Untyped
    go (pass , x , y) [] = step pass x (done y)
    go (pass , x , y) ((pass' , _ , z) ∷ xs) = step pass x (go (pass' , y , z) xs)
