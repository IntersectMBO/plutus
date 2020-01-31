{-# LANGUAGE TypeApplications #-}

module Language.PlutusTx.Evaluation
    ( evaluateCek
    , unsafeEvaluateCek
    , evaluateCekTrace
    , ErrorWithCause(..)
    , EvaluationError(..)
    , CekEvaluationException
    , Plain
    , ExBudget(..)
    , ExTally(..)
    , exBudgetStateBudget
    , exBudgetStateTally
    , exBudgetCPU
    , exBudgetMemory
    )
where

import           PlutusPrelude

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Evaluation.Machine.Cek hiding (evaluateCek, unsafeEvaluateCek)
import qualified Language.PlutusCore.Evaluation.Machine.Cek as PLC (evaluateCek, unsafeEvaluateCek)

import           Control.Exception
import           System.IO.Unsafe

stringBuiltins :: DynamicBuiltinNameMeanings
stringBuiltins =
    insertDynamicBuiltinNameDefinition dynamicCharToStringDefinition
        $ insertDynamicBuiltinNameDefinition dynamicAppendDefinition mempty

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins.
evaluateCek :: Program TyName Name () -> Either CekEvaluationException (Plain Term)
evaluateCek = PLC.evaluateCek stringBuiltins . toTerm

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins. May throw.
unsafeEvaluateCek :: Program TyName Name () -> EvaluationResultDef
unsafeEvaluateCek = PLC.unsafeEvaluateCek stringBuiltins . toTerm

-- TODO: pretty sure we shouldn't need the unsafePerformIOs here, we should expose a pure interface even if it has IO hacks under the hood

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins and tracing, additionally
-- returning the trace output.
evaluateCekTrace
    :: Program TyName Name ()
    -> ([String], ExTally, Either CekEvaluationException (Plain Term))
evaluateCekTrace p =
    let
        (lg, (res, state)) = unsafePerformIO $ withEmit $ \emit -> do
            let logName = dynamicTraceName
                logDefinition = dynamicCallAssign logName emit
                env = insertDynamicBuiltinNameDefinition logDefinition
                                                         stringBuiltins
            evaluate $ runCekCounting env $ toTerm p
    in  (lg, view exBudgetStateTally state, res)
