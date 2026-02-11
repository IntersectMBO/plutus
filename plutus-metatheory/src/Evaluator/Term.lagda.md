---
title: Term - Haskell Interface to the Metatheory
layout: page
---
# Haskell Interface to the metatheory

This module contains functions that are meant to be called from Haskell code.
It is mainly used by different testing programs.

```
module Evaluator.Term where
```

## Imports

```
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤;tt)
open import Function using (_$_;_∘_)
open import Data.Bool using (Bool)
open import Data.String using (String;_++_)
open import Data.Product using (_,_)

open import Type using (∅)

open import Check using (TypeError;inferType;inferKind;decKind;checkKind;checkType)
open TypeError

open import Scoped using (extricateScopeTy;Weirdℕ;scopeCheckTm;shifter;unshifter;extricateScope;unshifterTy;scopeCheckTy;shifterTy;FreeVariableError)
open Weirdℕ
open import Scoped.Extrication using (extricateNf⋆;extricate)
open import Utils using (Either;inj₁;inj₂;withE;Kind;*;Maybe;nothing;just;Monad;RuntimeError;dec2Either;_×_;_,_)
open RuntimeError
open Monad {{...}}

open import Raw using (RawTm;RawTy;rawPrinter;rawTyPrinter;decRTy;decRTm)
open import Raw using (rawPrinter;rawTyPrinter;decRTy;decRTm)
open import Algorithmic using (_⊢_;∅;error)
open import Algorithmic.CK using (stepper;State;Stack;ε)
open Algorithmic.CK.State

open import Algorithmic.CEK using (stepper;State;Stack;ε;Env;[])
open Algorithmic.CEK.State
import Algorithmic.Evaluation as L using (stepper)

import Untyped as U using (_⊢;scopeCheckU0;extricateU0;decUTm)
import RawU as U using (Untyped)
open import Untyped.CEK as U using (stepper;Stack;ε;Env;[];State)
open U.State
import Untyped.CEKWithCost as U using (stepperC)
open import Cost.Raw using (RawCostModel)
open import Cost.Model using (createMap)
open import Cost using (machineParameters;ExBudget)
open ExBudget


open import Evaluator.Base using (ERROR;uglyTypeError;maxsteps;ParseError)
open ERROR
```

## Imports from Haskell

```
{-# FOREIGN GHC import Data.Bifunctor #-}
{-# FOREIGN GHC import Data.Functor #-}
{-# FOREIGN GHC import Data.Either #-}
{-# FOREIGN GHC import Control.Monad.Trans.Except #-}
{-# FOREIGN GHC import Raw #-}
{-# FOREIGN GHC import PlutusCore #-}
{-# FOREIGN GHC import PlutusCore.DeBruijn #-}
{-# FOREIGN GHC import qualified UntypedPlutusCore as U #-}
{-# FOREIGN GHC import qualified UntypedPlutusCore.Parser as U #-}
{-# FOREIGN GHC import qualified FFI.Untyped as U #-}

postulate
  Term : Set
  Type : Set
  TermN  : Set
  TypeN  : Set
  TermNU : Set
  TermU  : Set

{-# COMPILE GHC Term = type PlutusCore.Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun () #-}
{-# COMPILE GHC Type = type PlutusCore.Type NamedTyDeBruijn DefaultUni () #-}
{-# COMPILE GHC TermN = type PlutusCore.Term TyName Name DefaultUni DefaultFun PlutusCore.SrcSpan #-}
{-# COMPILE GHC TypeN = type PlutusCore.Type TyName DefaultUni PlutusCore.SrcSpan #-}
{-# COMPILE GHC TermNU = type U.Term Name DefaultUni DefaultFun PlutusCore.SrcSpan #-}
{-# COMPILE GHC TermU = type U.Term NamedDeBruijn DefaultUni DefaultFun () #-}

postulate
  parseTm : String → Either ParseError TermN
  parseTmU : String → Either ParseError TermNU
  parseTy : String → Either ParseError TypeN
  deBruijnifyTm : TermN → Either FreeVariableError Term
  deBruijnifyTy : TypeN → Either FreeVariableError Type
  deBruijnifyTmU : TermNU → Either FreeVariableError TermU
  convTm : Term → RawTm
  unconvTm : RawTm → Term
  convTy : Type → RawTy
  unconvTy : RawTy → Type
  convTmU : TermU → U.Untyped
  unconvTmU : U.Untyped → TermU

{-# COMPILE GHC parseTm = runQuoteT . parseTerm #-}
{-# COMPILE GHC parseTmU = runQuoteT . U.parseTerm #-}
{-# COMPILE GHC parseTy = runQuoteT . parseType #-}
{-# COMPILE GHC deBruijnifyTm = second void . runExcept . deBruijnTerm #-}
{-# COMPILE GHC deBruijnifyTy = second void . runExcept . deBruijnTy #-}
{-# COMPILE GHC deBruijnifyTmU = second void . runExcept . U.deBruijnTerm #-}
{-# COMPILE GHC convTm = conv #-}
{-# COMPILE GHC unconvTm = unconv 0 #-}
{-# COMPILE GHC convTy = convT #-}
{-# COMPILE GHC unconvTy = unconvT 0 #-}
{-# COMPILE GHC convTmU = U.conv #-}
{-# COMPILE GHC unconvTmU = U.uconv 0 #-}

```

## Functions to be called from Haskell

A Haskell interface to the kindchecker:

```
checkKindX : Type → Kind → Either ERROR ⊤
checkKindX ty k = do
  ty        ← withE scopeError (scopeCheckTy (shifterTy Z (convTy ty)))
  (k' , _) ← withE (λ e → typeError (uglyTypeError e)) (inferKind ∅ ty)
  _         ← withE ((λ e → ERROR.typeError (uglyTypeError e)) ∘ kindMismatch _ _) (dec2Either (decKind k k'))
  return tt

{-# COMPILE GHC checkKindX as checkKindAgda #-}
```

A Haskell interface to kind inference:

```
inferKind∅ : Type → Either ERROR Kind
inferKind∅ ty = do
  ty       ← withE scopeError (scopeCheckTy (shifterTy Z (convTy ty)))
  (k , _) ← withE (λ e → typeError (uglyTypeError e)) (inferKind ∅ ty)
  return k

{-# COMPILE GHC inferKind∅ as inferKindAgda #-}
```

A Haskell interface to the type normalizer:
```
normalizeType : Type → Either ERROR Type
normalizeType ty = do
  ty'    ← withE scopeError (scopeCheckTy (shifterTy Z (convTy ty)))
  _ , n ← withE (λ e → typeError (uglyTypeError e)) (inferKind ∅ ty')
  return (unconvTy (unshifterTy Z (extricateScopeTy (extricateNf⋆ n))))

{-# COMPILE GHC normalizeType as normalizeTypeAgda #-}
```

Haskell interface to type checker:

```
inferType∅ : Term → Either ERROR Type
inferType∅ t = do
  t' ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  ty , _ ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ t')
  return (unconvTy (unshifterTy Z (extricateScopeTy (extricateNf⋆ ty))))

{-# COMPILE GHC inferType∅ as inferTypeAgda #-}

-- FIXME: we have a checkType function now...
checkType∅ : Type → Term → Either ERROR ⊤
checkType∅ ty t = do
  ty' ← withE scopeError (scopeCheckTy (shifterTy Z (convTy ty)))
  tyN ← withE (λ e → typeError (uglyTypeError e)) (checkKind ∅ ty' *)
  t'  ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  withE (λ e → typeError (uglyTypeError e)) (checkType ∅ t' tyN)
{-
  tyN' , tmC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ t')
  refl      ← withE ((λ e → typeError (uglyTypeError e)) ∘ kindMismatch _ _) (meqKind k *)
  refl      ← withE ((λ e → typeError (uglyTypeError e)) ∘ typeMismatch _ _) (meqNfTy tyN tyN')
-}
  return _
```

Haskell interface to type normalizer (for terms).
The type checker/inferer could also return such a term

```
normalizeTypeTerm : Term → Either ERROR Term
normalizeTypeTerm t = do
  tDB ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  _ , tC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ tDB)
  return (unconvTm (unshifter Z (extricateScope (extricate tC))))

{-# COMPILE GHC normalizeTypeTerm as normalizeTypeTermAgda #-}

{-# COMPILE GHC checkType∅ as checkTypeAgda #-}
```

 Haskell interface to (typechecked and proven correct) reduction

```
runTL : Term → Either ERROR Term
runTL t = do
  tDB ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  _ , tC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ tDB)
  t ← withE runtimeError $ L.stepper tC maxsteps
  return (unconvTm (unshifter Z (extricateScope (extricate t))))

{-# COMPILE GHC runTL as runTLAgda #-}
```

Note the interfaces to evaluation below catch userErrors and replace them with error terms

 Haskell interface to (typechecked) CK

```
runTCK : Term → Either ERROR Term
runTCK t = do
  tDB ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  ty , tC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ tDB)
  □ V ← withE runtimeError $ Algorithmic.CK.stepper maxsteps (ε ▻ tC)
    where (_ ▻ _) → inj₁ (runtimeError gasError)
          (_ ◅ _) → inj₁ (runtimeError gasError)
          ◆ A → return (unconvTm (unshifter Z (extricateScope {0}{Z} (extricate (error ty)))))
  return (unconvTm (unshifter Z (extricateScope (extricate (Algorithmic.CK.discharge V)))))

{-# COMPILE GHC runTCK as runTCKAgda #-}
```

Haskell interface to (typechecked) CEK

```
runTCEK : Term → Either ERROR Term
runTCEK t = do
  tDB ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  ty , tC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ tDB)
  □ V ← withE runtimeError $ Algorithmic.CEK.stepper maxsteps (ε ; [] ▻ tC)
    where (_ ; _ ▻ _) → inj₁ (runtimeError gasError)
          (_ ◅ _) → inj₁ (runtimeError gasError)
          ◆ A → return (unconvTm (unshifter Z (extricateScope {0}{Z} (extricate (error ty)))))
  return (unconvTm (unshifter Z (extricateScope (extricate (Algorithmic.CEK.discharge V)))))

{-# COMPILE GHC runTCEK as runTCEKAgda #-}
```

Note that according to the specification ◆ should reduce to an error term,
but here the untyped PLC term evaluator matches the behaviour of the
Haskell implementation: an error is thrown with ◆.

```
runUValue : _ U.⊢ → Either ERROR U.Value
runUValue t = do
  □ V ← withE runtimeError $ U.stepper maxsteps (ε ; [] ▻ t)
    where
    ◆ → inj₁ (runtimeError userError) -- ◆ returns a `userError` runtimeError.
    _ → inj₁ (runtimeError gasError)
  return V

runU : TermU → Either ERROR TermU
runU t = do
  tDB ← withE scopeError $ U.scopeCheckU0 (convTmU t)
  V   ← runUValue tDB
  return (unconvTmU (U.extricateU0 (U.discharge V)))

{-# COMPILE GHC runU as runUAgda #-}
```

Run an untyped term with costing in Counting mode.

From Haskell, this function should be called as `runUCountingAgda`
where the first argument is a `CostModel`, as defined in
`plutus-metatheory/src/Opts.hs` and the second argument is a
`Term NamedDeBruijn DefaultUni DefaultFun ()`.

From Haskell, the return type is either an error or a tuple
`(Term NamedDeBruijn DefaultUni DefaultFun (), (Integer, Integer))` consisting
of the result of evalution, and a pair of the CPU costs and the memory costs,
respectively.

```
runUCounting : RawCostModel → TermU → Either ERROR (TermU × (Nat × Nat))
runUCounting (cekMachineCosts , rawmodel) t with createMap rawmodel
... | just model = do
        tDB ← withE scopeError $ U.scopeCheckU0 (convTmU t)
        let params = machineParameters (cekMachineCosts , model)
            (ev , exBudget) = U.stepperC params maxsteps (ε ; [] ▻ tDB)
        □ V ← withE runtimeError ev
            where
            ◆ → inj₁ (runtimeError userError) -- ◆ returns a `userError` runtimeError.
            _ → inj₁ (runtimeError gasError)
        return (unconvTmU (U.extricateU0 (U.discharge V)) , (ExCPU exBudget , ExMem exBudget))
... | nothing = inj₁ (jsonError "while processing parameters.")

{-# COMPILE GHC runUCounting as runUCountingAgda #-}

```


```
blah : String → String → String
blah plc1 plc2 with parseTm plc1 | parseTm plc2
blah plc1 plc2 | inj₂ plc1' | inj₂ plc2' with deBruijnifyTm plc1' | deBruijnifyTm plc2'
blah plc1 plc2 | inj₂ plc1' | inj₂ plc2' | inj₂ plc1'' | inj₂ plc2'' = rawPrinter (convTm plc1'') ++ " || " ++ rawPrinter (convTm plc2'')
blah plc1 plc2 | inj₂ plc1' | inj₂ plc2' | _ | _ = "deBruijnifying failed"
blah plc1 plc2 | _ | _ = "parsing failed"

{-# COMPILE GHC blah as blah #-}

printTy : String → String
printTy b with parseTy b
... | inj₁ _ = "parseTy error"
... | inj₂ A  with deBruijnifyTy A
... | inj₁ _ = "deBruinjifyTy error"
... | inj₂ A' = rawTyPrinter (convTy A')

{-# COMPILE GHC printTy as printTy #-}

alphaTy : String → String → Bool
alphaTy plc1 plc2 with parseTy plc1 | parseTy plc2
alphaTy plc1 plc2 | inj₂ plc1' | inj₂ plc2' with deBruijnifyTy plc1' | deBruijnifyTy plc2'
alphaTy plc1 plc2 | inj₂ plc1' | inj₂ plc2' | inj₂ plc1'' | inj₂ plc2'' = decRTy (convTy plc1'') (convTy plc2'')
alphaTy plc1 plc2 | inj₂ plc1' | inj₂ plc2' | _ | _ = Bool.false
alphaTy plc1 plc2 | _ | _ = Bool.false

{-# COMPILE GHC alphaTy as alphaTy #-}

alphaTm : String → String → Bool
alphaTm plc1 plc2 with parseTm plc1 | parseTm plc2
alphaTm plc1 plc2 | inj₂ plc1' | inj₂ plc2' with deBruijnifyTm plc1' | deBruijnifyTm plc2'
alphaTm plc1 plc2 | inj₂ plc1' | inj₂ plc2' | inj₂ plc1'' | inj₂ plc2'' = decRTm (convTm plc1'') (convTm plc2'')
alphaTm plc1 plc2 | inj₂ plc1' | inj₂ plc2' | _ | _ = Bool.false
alphaTm plc1 plc2 | _ | _ = Bool.false

{-# COMPILE GHC alphaTm as alphaTm #-}

alphaU : String → String → Bool
alphaU plc1 plc2 with parseTmU plc1 | parseTmU plc2
alphaU plc1 plc2 | inj₂ plc1' | inj₂ plc2' with deBruijnifyTmU plc1' | deBruijnifyTmU plc2'
alphaU plc1 plc2 | inj₂ plc1' | inj₂ plc2' | inj₂ plc1'' | inj₂ plc2'' = U.decUTm (convTmU plc1'') (convTmU plc2'')
alphaU plc1 plc2 | inj₂ plc1' | inj₂ plc2' | _ | _ = Bool.false
alphaU plc1 plc2 | _ | _ = Bool.false

{-# COMPILE GHC alphaU as alphaU #-}
```
