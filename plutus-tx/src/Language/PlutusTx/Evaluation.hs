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

import           Language.PlutusCore.Builtins
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import           Language.UntypedPlutusCore
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek hiding (evaluateCek, unsafeEvaluateCek)
import qualified Language.UntypedPlutusCore.Evaluation.Machine.Cek as UPLC

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins.
evaluateCek
    :: (uni ~ DefaultUni, fun ~ DefaultFun)
    => Program Name uni fun () -> Either (CekEvaluationException uni fun) (Term Name uni fun ())
evaluateCek (Program _ _ t) = UPLC.evaluateCekNoEmit defBuiltinsRuntime t

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins. May throw.
unsafeEvaluateCek
    :: (uni ~ DefaultUni, fun ~ DefaultFun)
    => Program Name uni fun () -> EvaluationResult (Term Name uni fun ())
unsafeEvaluateCek (Program _ _ t) = UPLC.unsafeEvaluateCekNoEmit defBuiltinsRuntime t

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins and tracing, additionally
-- returning the trace output.
evaluateCekTrace
    :: (uni ~ DefaultUni, fun ~ DefaultFun)
    => Program Name uni fun ()
    -> ([String], CekExTally fun, Either (CekEvaluationException uni fun) (Term Name uni fun ()))
evaluateCekTrace (Program _ _ t) =
    case runCek defBuiltinsRuntime tallying True t of
        (errOrRes, TallyingSt st _, logs) -> (logs, st, errOrRes)
