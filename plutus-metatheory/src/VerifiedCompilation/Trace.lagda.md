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

### IMPORTANT
The order of the constructors in both their Agda definitions and in the "COMPILE"
pragmas MUST be the same as the order of their counterparts in
`UntypedPlutusCore.Transform.Certify.Trace`.
```

data UncertifiedOptTag : Set where
  caseOfCaseT : UncertifiedOptTag
  constantFoldingT : UncertifiedOptTag

data CertifiedOptTag : Set where
  floatDelayT : CertifiedOptTag
  forceDelayT : CertifiedOptTag
  forceCaseDelayT : CertifiedOptTag
  inlineT : CertifiedOptTag
  cseT : CertifiedOptTag
  applyToCaseT : CertifiedOptTag
  caseReduceT : CertifiedOptTag
  letFloatOutT : CertifiedOptTag
  polyBuiltinT : CertifiedOptTag

OptTag = Utils.Either UncertifiedOptTag CertifiedOptTag

FloatDelayT : OptTag
FloatDelayT = Utils.inj₂ floatDelayT
ForceDelayT : OptTag
ForceDelayT = Utils.inj₂ forceDelayT
ForceCaseDelayT : OptTag
ForceCaseDelayT = Utils.inj₂ forceCaseDelayT
InlineT : OptTag
InlineT = Utils.inj₂ inlineT
CseT : OptTag
CseT = Utils.inj₂ cseT
ApplyToCaseT : OptTag
ApplyToCaseT = Utils.inj₂ applyToCaseT
LetFloatOutT : OptTag
LetFloatOutT = Utils.inj₂ letFloatOutT
CaseReduceT : OptTag
CaseReduceT = Utils.inj₂ caseReduceT

CaseOfCaseT : OptTag
CaseOfCaseT = Utils.inj₁ caseOfCaseT
ConstantFoldingT : OptTag
ConstantFoldingT = Utils.inj₁ constantFoldingT
PolyBuiltinT : OptTag
PolyBuiltinT = Utils.inj₂ polyBuiltinT

{-# COMPILE GHC
  CertifiedOptTag
    = data CertifiedOptStage
      ( FloatDelay
      | ForceDelay
      | ForceCaseDelay
      | Inline
      | CSE
      | ApplyToCase
      | CaseReduce
      | LetFloatOut
      | PolyBuiltin
      )
#-}
{-# COMPILE GHC
  UncertifiedOptTag
    = data UncertifiedOptStage
      ( CaseOfCase
      | ConstantFolding
      )
#-}
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

A `NonEmptySep S A` is a non-empty list of values of type `A`, separated by
values of type `S`. 
```

data NonEmptySep (S A : Set) : Set where
  cons : A → S → NonEmptySep S A → NonEmptySep S A
  singleton : A → NonEmptySep S A

{-# FOREIGN GHC import qualified Data.List.NonEmptySep as NES #-}
{-# COMPILE GHC NonEmptySep = data NES.NonEmptySep (NES.Cons | NES.Singleton) #-}

pattern _∷[_]_ x y xs = cons x y xs
infixr 5 _∷[_]_

-- Get the first term in the trace
head : ∀{S A} → NonEmptySep S A → A
head (singleton x) = x
head (cons x _ _) = x
```

A `Trace A` is a sequence of optimisation transformations applied to terms of
AST type `A`. Each transition is labeled with a `OptTag` and `Hints` that have
information about which pass was performed.

```
-- An optimizer trace, parametrized by the AST type
Trace : Set → Set
Trace A = NonEmptySep (OptTag × Hints) A
```

`EvalResult` is used to report script execution costs, before and after an optimisation (or optimisations).

```
data EvalResult : Set where
  success : ℕ → ℕ → EvalResult
  failure : String → ℕ → ℕ → EvalResult

{-# FOREIGN GHC import FFI.CostInfo #-}
{-# COMPILE GHC EvalResult = data EvalResult (EvalSuccess | EvalFailure) #-}
```
