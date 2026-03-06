---
title: Main
layout: page
---
```
module Main where

import Certifier
import VerifiedCompilation
open import Agda.Builtin.IO using (IO)
import IO.Primitive.Core as IO using (return;_>>=_)
open import Agda.Builtin.Unit using (⊤;tt)
open import Function using (_$_;_∘_)
open import Data.String using (String;_++_)
open import Agda.Builtin.Nat
open import Agda.Builtin.Int using (pos)
open import Data.Integer.Show using (show)
open import Data.Product using (Σ) renaming (_,_ to _,,_)
open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Empty using (⊥)

open import Type using (Ctx⋆;∅;_,⋆_)
open import Check using (TypeError;inferType;inferKind;decKind;checkKind;checkType)
open TypeError -- Bring all TypeError constructors in scope.

open import Scoped.Extrication using (extricateNf⋆;extricate)
open import Type.BetaNormal using (_⊢Nf⋆_)
import Untyped as U using (_⊢;scopeCheckU0;extricateU0;decUTm)
import Untyped.CEKWithCost as U using (stepperC)
open import Cost.Base
open import Cost using (machineParameters;tallyingMachineParameters;countingReport;tallyingReport)
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

open import Evaluator.Base using (ERROR;reportError)
open import Evaluator.Program using (Input;Format;EvalMode;BudgetMode;ProgramN;ProgramNU;evalProgramNU;evalProgramN;typeCheckProgramN)
open EvalMode
import Evaluator.Term -- Needed only to generate the compiled Haskell file

-- There's a long prelude here that could go in a different file but
-- currently it's only used here

-- Text Stuff

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as TextIO #-}
{-# COMPILE GHC putStrLn = TextIO.putStrLn #-}

-- IO Stuff

instance
  IOMonad : Monad IO
  IOMonad = record { return = IO.return; _>>=_ = IO._>>=_ }

-- Parsing stuff

postulate
  FilePath : Set

{-# COMPILE GHC FilePath = type FilePath #-}

-- System.Exit stuff

postulate
  exitFailure : IO ⊤
  exitSuccess : IO ⊤

{-# FOREIGN GHC import System.Exit #-}
{-# COMPILE GHC exitSuccess = exitSuccess #-}
{-# COMPILE GHC exitFailure = exitFailure #-}

-- Input Options stuff
{-# FOREIGN GHC import FFI.Opts #-}

data EvalOptions (A : Set) : Set where
  EvalOpts : Input → Format → EvalMode → BudgetMode A → EvalOptions A

{-# COMPILE GHC EvalOptions = data EvalOptions (EvalOpts) #-}

data TypecheckOptions : Set where
  TCOpts : Input → Format → TypecheckOptions

{-# COMPILE GHC TypecheckOptions = data TypecheckOptions (TCOpts) #-}

data Command (A : Set) : Set where
  Eval  : EvalOptions A → Command A
  Typecheck : TypecheckOptions → Command A

{-# COMPILE GHC Command = data Command (Eval | Typecheck) #-}

{-# FOREIGN GHC import PlutusCore.Executable.Common  #-}
{-# FOREIGN GHC import PlutusCore.Executable.Parsers #-}

postulate
   execP : IO (Command RawCostModel)
   parse : Format → Input → IO ProgramN
   parseU : Format → Input → IO ProgramNU

{-# COMPILE GHC execP = execP #-}
{-# COMPILE GHC parse = readProgram #-}
{-# COMPILE GHC parseU = readProgram #-}

evalInput : EvalMode →  BudgetMode RawCostModel → Format → Input → IO (Either ERROR String)
evalInput U bm fmt inp = fmap (evalProgramNU bm) (parseU fmt inp)
evalInput m _ fmt inp  = fmap (evalProgramN m) (parse fmt inp)

tcInput : Format → Input → IO (Either ERROR String)
tcInput fmt inp = fmap typeCheckProgramN (parse fmt inp)

main' : Command RawCostModel → IO ⊤
main' (Eval (EvalOpts inp fmt m bm)) = do
  inj₂ s ← evalInput m bm fmt inp
    where
    inj₁ e → putStrLn (reportError e) >> exitFailure
  putStrLn s >> exitSuccess
main' (Typecheck (TCOpts inp fmt))    = do
  inj₂ s ← tcInput fmt inp
    where
    inj₁ e → putStrLn (reportError e) >> exitFailure
  putStrLn s >> exitSuccess

main : IO ⊤
main = execP >>= main'
```
