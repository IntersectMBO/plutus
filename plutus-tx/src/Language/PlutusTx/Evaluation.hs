{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}

module Language.PlutusTx.Evaluation
    ( evaluateCek
    , unsafeEvaluateCek
    , evaluateCekTrace
    , ErrorWithCause(..)
    , EvaluationError(..)
    , ExTally
    , CekEvaluationException
    , Plain
    )
where

import           PlutusPrelude

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Constant.Dynamic
import           Language.PlutusCore.Evaluation.Machine.Cek                 hiding (evaluateCek, unsafeEvaluateCek)
import qualified Language.PlutusCore.Evaluation.Machine.Cek                 as PLC (evaluateCek, unsafeEvaluateCek)
import qualified Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults as PLC
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Pretty                                 (PrettyConst)

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
    => Program TyName Name uni () -> Either (CekEvaluationException uni) (Plain Term uni)
evaluateCek = PLC.evaluateCek stringBuiltins PLC.defaultCostModel . toTerm

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins. May throw.
unsafeEvaluateCek
    :: ( GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage
       , Typeable uni, uni `Everywhere` PrettyConst
       )
    => Program TyName Name uni () -> EvaluationResult (Plain Term uni)
unsafeEvaluateCek = PLC.unsafeEvaluateCek stringBuiltins PLC.defaultCostModel . toTerm

-- TODO: pretty sure we shouldn't need the unsafePerformIOs here, we should expose a pure interface even if it has IO hacks under the hood

-- | Evaluate a program in the CEK machine with the usual string dynamic builtins and tracing, additionally
-- returning the trace output.
evaluateCekTrace
    :: (GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage)
    => Program TyName Name uni ()
    -> ([String], ExTally, Either (CekEvaluationException uni) (Plain Term uni))
evaluateCekTrace p =
    let
        (lg, (res, state)) = unsafePerformIO $ withEmit $ \emit -> do
            let logName = dynamicTraceName
                logDefinition = dynamicCallAssign logName emit (\_ -> ExBudget 1 1)
                env = insertDynamicBuiltinNameDefinition logDefinition
                                                         stringBuiltins
            Control.Exception.evaluate $ runCekCounting env PLC.defaultCostModel $ toTerm p
    in  (lg, view exBudgetStateTally state, res)
