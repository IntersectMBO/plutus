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

import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Pretty                                 (PrettyConst)

import           Control.Monad.Except

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckAnd
    :: (MonadError (Error uni ()) m, GShow uni, GEq uni, DefaultUni <: uni)
    => (DynamicBuiltinNameMeanings (Term TyName Name uni ann) -> CostModel -> Term TyName Name uni () -> a)
    -> DynamicBuiltinNameMeanings (Term TyName Name uni ann) -> Term TyName Name uni () -> m a
typecheckAnd action meanings term = runQuoteT $ do
    types <- dynamicBuiltinNameMeaningsToTypes () meanings
    _ <- inferType (TypeCheckConfig types) term
    -- The bang is important in order to force the effects of a computation regardless of whether
    -- the result of the computation is forced or not.
    return $! action meanings defaultCostModel term

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckEvaluateCek
    :: ( MonadError (Error uni ()) m, GShow uni, GEq uni, DefaultUni <: uni
       , Closed uni, uni `Everywhere` ExMemoryUsage, Typeable uni, uni `Everywhere` PrettyConst
       )
    => DynamicBuiltinNameMeanings (Term TyName Name uni ExMemory)
    -> Term TyName Name uni ()
    -> m (EvaluationResult (Term TyName Name uni ()))
typecheckEvaluateCek = typecheckAnd unsafeEvaluateCek

-- | Type check and convert a Plutus Core term to a Haskell value.
typecheckReadKnownCek
    :: ( MonadError (Error uni ()) m, KnownType (Term TyName Name uni ()) a
       , GShow uni, GEq uni, DefaultUni <: uni, Closed uni, uni `Everywhere` ExMemoryUsage
       )
    => DynamicBuiltinNameMeanings (Term TyName Name uni ExMemory)
    -> Term TyName Name uni ()
    -> m (Either (CekEvaluationException uni) a)
typecheckReadKnownCek = typecheckAnd readKnownCek
