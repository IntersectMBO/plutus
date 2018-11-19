{-# LANGUAGE FlexibleContexts #-}

module DynamicBuiltins.Common
    ( typecheckEvaluate
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Language.PlutusCore.Interpreter.CekMachine

import           Control.Monad.Except

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckEvaluate
    :: (MonadError (Error ()) m, MonadQuote m)
    => DynamicBuiltinNameMeanings -> Term TyName Name () -> m EvaluationResult
typecheckEvaluate meanings term = do
    let types = dynamicBuiltinNameMeaningsToTypes meanings
    _ <- annotateTerm term >>= typecheckTerm (TypeCheckCfg 1000 $ TypeConfig True types)
    return $ evaluateCek meanings term
