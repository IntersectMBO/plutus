{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
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

import           Language.PlutusCore.Constant
import           Language.PlutusCore.Constant.Dynamic
import qualified Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults as PLC
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty                                 (PrettyConst)
import           Language.PlutusCore.Universe

import           Language.UntypedPlutusCore
import           Language.UntypedPlutusCore.Evaluation.Machine.Cek          hiding (evaluateCek, unsafeEvaluateCek)
import qualified Language.UntypedPlutusCore.Evaluation.Machine.Cek          as UPLC (evaluateCek, unsafeEvaluateCek)

import qualified Control.Exception
import           System.IO.Unsafe

stringBuiltins
    :: ( GShow uni, GEq uni, uni `IncludesAll` '[String, Char, ()]
       , Closed uni, uni `Everywhere` ExMemoryUsage
       )
    => DynamicBuiltinNameMeanings (CekValue uni)
stringBuiltins =
    insertDynamicBuiltinNameDefinition dynamicCharToStringDefinition
        $ insertDynamicBuiltinNameDefinition dynamicAppendDefinition mempty

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins.
evaluateCek
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Program Name uni () -> Either (CekEvaluationException uni) (Term Name uni ())
evaluateCek (Program _ _ t) = UPLC.evaluateCek stringBuiltins PLC.defaultCostModel t

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins. May throw.
unsafeEvaluateCek
    :: ( GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Typeable uni, uni `Everywhere` PrettyConst
       )
    => Program Name uni () -> EvaluationResult (Term Name uni ())
unsafeEvaluateCek (Program _ _ t) = UPLC.unsafeEvaluateCek stringBuiltins PLC.defaultCostModel t

-- TODO: pretty sure we shouldn't need the unsafePerformIOs here, we should expose a pure interface even if it has IO hacks under the hood

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins and tracing, additionally
-- returning the trace output.
evaluateCekTrace
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Program Name uni ()
    -> ([String], CekExTally, Either (CekEvaluationException uni) (Term Name uni ()))
evaluateCekTrace (Program _ _ t) =
    let
        (lg, (res, state)) = unsafePerformIO $ withEmit $ \emit -> do
            let logName = dynamicTraceName
                logDefinition = dynamicCallAssign logName emit (\_ -> ExBudget 1 1)
                env = insertDynamicBuiltinNameDefinition logDefinition
                                                         stringBuiltins
            Control.Exception.evaluate $ runCekCounting env PLC.defaultCostModel t
    in  (lg, view exBudgetStateTally state, res)
