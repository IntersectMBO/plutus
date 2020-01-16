{-# LANGUAGE TypeApplications #-}

module Language.PlutusTx.Evaluation
    ( evaluateCek
    , unsafeEvaluateCek
    , evaluateCekTrace
    , CekMachineException(..)
    , Plain
    , ExBudget(..)
    , ExTally(..)
    , exBudgetStateBudget
    , exBudgetStateTally
    , exBudgetCPU
    , exBudgetMemory
    , exTallyMemory
    , exTallyCPU
    )
where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Evaluation.Machine.Cek      hiding (evaluateCek, unsafeEvaluateCek)
import           Language.PlutusCore.Evaluation.Machine.ExMemory

import           Control.Exception
import           Control.Lens.Combinators                        (_1)
import           PlutusPrelude

import           System.IO.Unsafe

stringBuiltins :: DynamicBuiltinNameMeanings
stringBuiltins =
    insertDynamicBuiltinNameDefinition dynamicCharToStringDefinition
        $ insertDynamicBuiltinNameDefinition dynamicAppendDefinition mempty

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins.
evaluateCek :: Program TyName Name () -> Either CekMachineException (Plain Term)
evaluateCek = view _1 . runCek stringBuiltins Counting mempty -- TODO debug output?

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins. May throw.
unsafeEvaluateCek :: Program TyName Name () -> Term TyName Name ()
unsafeEvaluateCek = unsafeRunCek stringBuiltins

-- TODO: pretty sure we shouldn't need the unsafePerformIOs here, we should expose a pure interface even if it has IO hacks under the hood

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins and tracing, additionally
-- returning the trace output.
evaluateCekTrace
    :: Program TyName Name ()
    -> ([String], ExTally, Either CekMachineException (Plain Term))
evaluateCekTrace p =
    let
        (lg, (res, state)) = unsafePerformIO $ withEmit $ \emit -> do
            let logName = dynamicTraceName
                logDefinition = dynamicCallAssign logName emit
                env = insertDynamicBuiltinNameDefinition logDefinition
                                                         stringBuiltins
            evaluate $ runCek env Counting mempty p
    in  (lg, view exBudgetStateTally state, res)
