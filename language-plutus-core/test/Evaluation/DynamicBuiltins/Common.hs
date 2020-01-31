{-# LANGUAGE FlexibleContexts #-}

module Evaluation.DynamicBuiltins.Common
    ( typecheckEvaluateCek
    , typecheckReadKnownCek
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Language.PlutusCore.Evaluation.Machine.Cek

import           Control.Monad.Except

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckAnd
    :: MonadError (Error ()) m
    => (DynamicBuiltinNameMeanings -> Term TyName Name () -> a)
    -> DynamicBuiltinNameMeanings -> Term TyName Name () -> m a
typecheckAnd action meanings term = runQuoteT $ do
    types <- dynamicBuiltinNameMeaningsToTypes () meanings
    _ <- inferType (offChainConfig types) term
    -- The bang is important in order to force the effects of a computation regardless of whether
    -- the result of the computation is forced or not.
    return $! action meanings term

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckEvaluateCek
    :: MonadError (Error ()) m
    => DynamicBuiltinNameMeanings -> Term TyName Name () -> m EvaluationResultDef
typecheckEvaluateCek = typecheckAnd unsafeEvaluateCek

-- | Type check and convert a Plutus Core term to a Haskell value.
typecheckReadKnownCek
    :: (MonadError (Error ()) m, KnownType a)
    => DynamicBuiltinNameMeanings
    -> Term TyName Name ()
    -> m (Either CekEvaluationException a)
typecheckReadKnownCek = typecheckAnd readKnownCek
