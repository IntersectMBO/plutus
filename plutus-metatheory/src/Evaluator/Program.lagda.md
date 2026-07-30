---
title: Program Evaluators
layout: page
---
# Evaluators for Programs

```
module Evaluator.Program where
```

## Imports

```
open import Function using (_$_;_∘_)
open import Data.String using (String;_++_)
open import Agda.Builtin.Nat
open import Data.Product using (Σ) renaming (_,_ to _,,_)
open import Data.Empty using (⊥)

open import Type using (Ctx⋆;∅;_,⋆_)
open import Check using (TypeError;inferType;inferKind;decKind;checkKind;checkType)
open TypeError -- Bring all TypeError constructors in scope.

open import Scoped.Extrication using (extricateNf⋆;extricate)
open import Type.BetaNormal using (_⊢Nf⋆_)
import Untyped as U using (_⊢;scopeCheckU0;extricateU0;decUTm)
import Untyped.CEKWithCost as U using (stepperC)
open import Cost.Base
open import Cost using (ExBudget;machineParameters;tallyingMachineParameters;countingReport;tallyingReport;CostModel)
open import Cost.Raw using (RawCostModel)
open import Cost.Model using (createMap)
import RawU as U using (Untyped)

open import Untyped.CEK as U using (stepper;Stack;ε;Env;[];State)
open U.State

open import Raw using (RawTm;RawTy;rawPrinter;rawTyPrinter;decRTy;decRTm)
open import Scoped using (FreeVariableError;ScopeError;freeVariableError;extricateScopeTy;ScopedTm;Weirdℕ;scopeCheckTm;shifter;unshifter;extricateScope;unshifterTy;scopeCheckTy;shifterTy)
open Weirdℕ -- Bring Weirdℕ constructors in scope
open import Utils using (Either;inj₁;inj₂;withE;Kind;*;Maybe;nothing;just;Monad;RuntimeError;dec2Either;_,_)
open RuntimeError
open Monad {{...}}

open import Algorithmic using (_⊢_;∅;error)

open import Algorithmic.CK using (stepper;State;Stack;ε)
open Algorithmic.CK.State

open import Algorithmic.CEK using (stepper;State;Stack;ε;Env;[])
open Algorithmic.CEK.State

open import Algorithmic.Erasure using (erase)
import Algorithmic.Evaluation as L using(stepper)

open import Evaluator.Base using (ERROR;uglyTypeError;maxsteps;prettyPrintUTm;prettyPrintTm;prettyPrintTy;ParseError)
open ERROR
```

## Imports from Haskell

```
{-# FOREIGN GHC import PlutusCore.Executable.Common  #-}
{-# FOREIGN GHC import PlutusCore.Executable.Parsers #-}

postulate
   Format : Set
   Input : Set

{-# COMPILE GHC Format = type Format #-}
{-# COMPILE GHC Input = type Input #-}

postulate
  ProgramN : Set
  Program : Set
  convP : Program → RawTm
  deBruijnify : ProgramN → Either FreeVariableError Program

  ProgramNU : Set
  ProgramU : Set
  deBruijnifyU : ProgramNU → Either FreeVariableError ProgramU
  convPU : ProgramU → U.Untyped

{-# FOREIGN GHC import PlutusCore.DeBruijn #-}
{-# FOREIGN GHC import qualified UntypedPlutusCore as U #-}
{-# FOREIGN GHC import qualified UntypedPlutusCore.Parser as U #-}
{-# FOREIGN GHC import qualified FFI.Untyped as U #-}
{-# FOREIGN GHC import Raw #-}
{-# FOREIGN GHC import PlutusCore #-}
{-# FOREIGN GHC import Data.Bifunctor #-}
{-# FOREIGN GHC import Data.Functor #-}
{-# FOREIGN GHC import Data.Either #-}
{-# FOREIGN GHC import Control.Monad.Trans.Except #-}

{-# COMPILE GHC ProgramN = type PlutusCore.Program TyName Name DefaultUni DefaultFun PlutusCore.SrcSpan #-}
{-# COMPILE GHC Program = type PlutusCore.Program NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun () #-}
{-# COMPILE GHC convP = convP #-}
{-# COMPILE GHC deBruijnify = \ (Program ann ver tm) -> second (void . Program ann ver) . runExcept $ deBruijnTerm tm #-}

{-# COMPILE GHC ProgramNU = type U.Program Name DefaultUni DefaultFun PlutusCore.SrcSpan #-}
{-# COMPILE GHC ProgramU = type U.Program NamedDeBruijn DefaultUni DefaultFun () #-}
{-# COMPILE GHC deBruijnifyU = \ (U.Program ann ver tm) -> second (void . U.Program ann ver) . runExcept $ U.deBruijnTerm tm #-}
{-# COMPILE GHC convPU = U.convP #-}

{-# FOREIGN GHC import FFI.Opts #-}
```

## Evaluators

```
data BudgetMode (A : Set) : Set where
  Silent   : BudgetMode A
  Counting : A → BudgetMode A
  Tallying : A → BudgetMode A

{-# COMPILE GHC BudgetMode = data BudgetMode (Silent | Counting | Tallying) #-}

data EvalMode : Set where
  U TL TCK TCEK : EvalMode

{-# COMPILE GHC EvalMode = data EvalMode (U | TL | TCK | TCEK) #-}

parsePLC : ProgramN → Either ERROR (ScopedTm Z)
parsePLC namedprog = do
  prog ← withE (ERROR.scopeError ∘ freeVariableError) $ deBruijnify namedprog
  withE scopeError $ scopeCheckTm {0}{Z} (shifter Z (convP prog))
  -- ^ FIXME: this should have an interface that guarantees that the
  -- shifter is run

parseUPLC : ProgramNU → Either ERROR (0 U.⊢)
parseUPLC namedprog = do
  prog ← withE (ERROR.scopeError ∘ freeVariableError) $ deBruijnifyU namedprog
  withE scopeError $ U.scopeCheckU0 (convPU prog)

typeCheckPLC : ScopedTm Z → Either TypeError (Σ (∅ ⊢Nf⋆ *) (∅ ⊢_))
typeCheckPLC t = inferType _ t
```

Check if the term is an error term, and in that case return an ERROR.

This is used when evaluation of the reduction semantics has ended

```
checkError : ∀{A} → ∅ ⊢ A → Either ERROR (∅ ⊢ A )
checkError (error _) = inj₁ (runtimeError userError)
checkError t         = return t

executePLC : EvalMode → ScopedTm Z → Either ERROR String
executePLC U t = do
  (A ,, t) ← withE (λ e → typeError (uglyTypeError e)) $ typeCheckPLC t
  □ V ← withE runtimeError $ U.stepper maxsteps (ε ; [] ▻ erase t)
    where ◆  → inj₁ (runtimeError userError)
          _  → inj₁ (runtimeError gasError)
{-
just t' ← withE runtimeError $ U.stepper maxsteps (ε ; [] ▻ erase t)
    where nothing → inj₁ (runtimeError userError)
    -}
  return $ prettyPrintUTm (U.extricateU0 (U.discharge V))
executePLC TL t = do
  (A ,, t) ← withE (λ e → typeError (uglyTypeError e)) $ typeCheckPLC t
  t' ← (withE runtimeError $ L.stepper t maxsteps) >>= checkError
  return (prettyPrintTm (unshifter Z (extricateScope (extricate t'))))
executePLC TCK t = do
  (A ,, t) ← withE (λ e → typeError (uglyTypeError e)) $ typeCheckPLC t
  □ {t = t} v ← withE runtimeError $ Algorithmic.CK.stepper maxsteps (ε ▻ t)
    where ◆ _  → inj₁ (runtimeError userError)
          _    → inj₁ (runtimeError gasError)
  return (prettyPrintTm (unshifter Z (extricateScope (extricate t))))
executePLC TCEK t = do
  (A ,, t) ← withE (λ e → typeError (uglyTypeError e)) $ typeCheckPLC t
  □ V ← withE runtimeError $ Algorithmic.CEK.stepper maxsteps (ε ; [] ▻ t)
    where ◆ _  → inj₁ (runtimeError userError)
          _    → inj₁ (runtimeError gasError)
  return (prettyPrintTm (unshifter Z (extricateScope (extricate (Algorithmic.CEK.discharge V)))))

showUPLCResult : U.State → Either ERROR String
showUPLCResult (□ V) = return $ prettyPrintUTm (U.extricateU0 (U.discharge V))
showUPLCResult ◆     = inj₁ (runtimeError userError)
showUPLCResult _     = inj₁ (runtimeError gasError)

executeUPLCwithMP : ∀{A} → RawCostModel → (CostModel → MachineParameters A) → (A → String) → 0 U.⊢ → Either ERROR String
executeUPLCwithMP (cekMachineCosts , rawmodel) mkMP report t with createMap rawmodel
... | just model = do
    let machineparam = mkMP (cekMachineCosts , model)
    let (ev , exBudget) = U.stepperC machineparam maxsteps (ε ; [] ▻ t)
    x ← withE runtimeError ev
    r ← showUPLCResult x
    return (r ++ report exBudget)
... | nothing = inj₁ (jsonError "while processing parameters.")

executeUPLC : BudgetMode RawCostModel → 0 U.⊢ → Either ERROR String
executeUPLC Silent t = (withE runtimeError $ U.stepper maxsteps (ε ; [] ▻ t)) >>= showUPLCResult
executeUPLC (Counting rcm) t = executeUPLCwithMP rcm machineParameters countingReport t
executeUPLC (Tallying rcm) t = executeUPLCwithMP rcm tallyingMachineParameters tallyingReport t

evalProgramNU : BudgetMode RawCostModel → ProgramNU → Either ERROR String
evalProgramNU bm namedprog = do
  t ← parseUPLC namedprog
  executeUPLC bm t

evalProgramN : EvalMode → ProgramN → Either ERROR String
evalProgramN m namedprog = do
  {-
  -- some debugging code
  prog ← withE (ERROR.scopeError ∘ freeVariableError) $ deBruijnify namedprog
  let shiftedprog = shifter Z (convP prog)
  scopedprog ← withE scopeError $ scopeCheckTm {0}{Z} shiftedprog
  let extricatedprog = extricateScope scopedprog
  let unshiftedprog = unshifter Z extricatedprog
  return ("orginal: " ++ rawPrinter (convP prog) ++ "\n" ++
          "shifted: " ++ rawPrinter shiftedprog ++ "\n" ++
          "instrinsically scoped: " ++ Scoped.ugly scopedprog ++ "\n" ++
          "extricated: " ++ rawPrinter extricatedprog ++ "\n" ++
          "unshifted: " ++ rawPrinter unshiftedprog ++ "\n" ++
          "unconved: " ++ prettyPrintTm unshiftedprog ++ "\n")
   -}
   t ← parsePLC namedprog
   executePLC m t

typeCheckProgramN : ProgramN → Either ERROR String
typeCheckProgramN namedprog = do
  t ← parsePLC namedprog
  (A ,, _) ← withE (λ e → typeError (uglyTypeError e) ) $ typeCheckPLC t
{-
  -- some debugging code
  let extricatedtype = extricateScopeTy (extricateNf⋆ A)
  let unshiftedtype = unshifterTy Z extricatedtype
  return ("original: " ++ "???" ++ "\n" ++
          "extricated: " ++ rawTyPrinter extricatedtype ++ "\n" ++
          "unshifted: " ++ rawTyPrinter unshiftedtype ++ "\n" ++
          "unconved: " ++ prettyPrintTy unshiftedtype ++ "\n")
 -}
  return (prettyPrintTy (unshifterTy Z (extricateScopeTy (extricateNf⋆ A))))
```

