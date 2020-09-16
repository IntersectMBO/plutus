{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators    #-}

module Evaluation.DynamicBuiltins.Common
    ( typecheckAnd
    , typecheckEvaluateCek
    , typecheckReadKnownCek
    ) where

import           PlutusPrelude

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Pretty

import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.ExMemory

import           Control.Monad.Except

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckAnd
    :: (MonadError (Error uni fun ()) m, GShow uni, GEq uni, DefaultUni <: uni)
    => (DynamicBuiltinNameMeanings (CekValue uni fun) -> CostModel -> Term TyName Name uni fun () -> a)
    -> DynamicBuiltinNameMeanings (CekValue uni fun) -> Term TyName Name uni fun () -> m a
typecheckAnd action meanings term = runQuoteT $ do
    types <- dynamicBuiltinNameMeaningsToTypes () meanings
    _ <- inferType (TypeCheckConfig types) term
    -- The bang is important in order to force the effects of a computation regardless of whether
    -- the result of the computation is forced or not.
    return $! action meanings defaultCostModel term

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckEvaluateCek
    :: ( MonadError (Error uni fun ()) m, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` ExMemoryUsage
       , uni `Everywhere` PrettyConst, Typeable uni, Typeable fun
       )
    => DynamicBuiltinNameMeanings (CekValue uni fun)
    -> Term TyName Name uni fun ()
    -> m (EvaluationResult (Term TyName Name uni fun ()))
typecheckEvaluateCek = typecheckAnd unsafeEvaluateCek

-- | Type check and convert a Plutus Core term to a Haskell value.
typecheckReadKnownCek
    :: ( MonadError (Error uni fun ()) m, KnownType (Term TyName Name uni fun ()) a
       , GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage
       )
    => DynamicBuiltinNameMeanings (CekValue uni fun)
    -> Term TyName Name uni fun ()
    -> m (Either (CekEvaluationException uni fun) a)
typecheckReadKnownCek = typecheckAnd readKnownCek
