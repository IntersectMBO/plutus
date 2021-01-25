{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Language.PlutusTx.Evaluation
    ( evaluateCek
    , unsafeEvaluateCek
    , evaluateCekTrace
    , ErrorWithCause(..)
    , EvaluationError(..)
    , CekExTally
    , CekEvaluationException
    , Plain
    )
where

import           PlutusPrelude

import           Language.PlutusCore.Builtins
import           Language.PlutusCore.Constant
import qualified Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults as PLC
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import           Language.UntypedPlutusCore
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek          hiding (evaluateCek, unsafeEvaluateCek)
import qualified Language.UntypedPlutusCore.Evaluation.Machine.Cek          as UPLC (evaluateCek, unsafeEvaluateCek)

import qualified Control.Exception
import qualified Data.Text                                                  as T
import           System.IO.Unsafe

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins.
evaluateCek
    :: (uni ~ DefaultUni, fun ~ DefaultFun)
    => Program Name uni fun () -> Either (CekEvaluationException uni fun) (Term Name uni fun ())
evaluateCek (Program _ _ t) = UPLC.evaluateCek defBuiltinsRuntime t

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins. May throw.
unsafeEvaluateCek
    :: (uni ~ DefaultUni, fun ~ DefaultFun)
    => Program Name uni fun () -> EvaluationResult (Term Name uni fun ())
unsafeEvaluateCek (Program _ _ t) = UPLC.unsafeEvaluateCek defBuiltinsRuntime t

-- TODO: pretty sure we shouldn't need the unsafePerformIOs here, we should expose a pure interface even if it has IO hacks under the hood

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins and tracing, additionally
-- returning the trace output.
evaluateCekTrace
    :: (uni ~ DefaultUni, fun ~ DefaultFun)
    => Program Name uni fun ()
    -> ([T.Text], CekExTally fun, Either (CekEvaluationException uni fun) (Term Name uni fun ()))
evaluateCekTrace (Program _ _ t) =
    let
        (lg, (res, state)) = unsafePerformIO $ withEmit $ \emit -> do
            let runtime = toBuiltinsRuntime (DefaultFunDyn emit) PLC.defaultCostModel
            Control.Exception.evaluate $ runCekCounting runtime t
    in  (lg, view exBudgetStateTally state, res)
