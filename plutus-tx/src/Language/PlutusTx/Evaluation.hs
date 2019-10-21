module Language.PlutusTx.Evaluation (evaluateCek, evaluateCekThrow, evaluateCekTrace, CekMachineException) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Interpreter.CekMachine hiding (evaluateCek)

import           Control.Exception

import           System.IO.Unsafe

stringBuiltins :: DynamicBuiltinNameMeanings
stringBuiltins =
    insertDynamicBuiltinNameDefinition dynamicCharToStringDefinition $ insertDynamicBuiltinNameDefinition dynamicAppendDefinition mempty

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins.
evaluateCek
    :: Program TyName Name ()
    -> Either CekMachineException EvaluationResultDef
evaluateCek = runCekCatch stringBuiltins

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins.
evaluateCekThrow
    :: Program TyName Name ()
    -> EvaluationResultDef
evaluateCekThrow = runCek stringBuiltins

-- TODO: pretty sure we shouldn't need the unsafePerformIOs here, we should expose a pure interface even if it has IO hacks under the hood

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins and tracing, additionally
-- returning the trace output.
evaluateCekTrace
    :: Program TyName Name ()
    -> ([String], Either CekMachineException EvaluationResultDef)
evaluateCekTrace p =
    unsafePerformIO $ withEmit $ \emit -> do
        let logName       = dynamicTraceName
            logDefinition = dynamicCallAssign logName emit
            env  = insertDynamicBuiltinNameDefinition logDefinition stringBuiltins
        evaluate $ runCekCatch env p
