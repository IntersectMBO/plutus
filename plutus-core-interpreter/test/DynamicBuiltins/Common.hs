{-# LANGUAGE FlexibleContexts #-}

module DynamicBuiltins.Common
    ( typecheckEvaluateCek
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Language.PlutusCore.Interpreter.CekMachine

import           Control.Monad.Except

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckEvaluateCek
    :: MonadError (Error ()) m
    => DynamicBuiltinNameMeanings -> Term TyName Name () -> m EvaluationResult
typecheckEvaluateCek meanings term = do
    let types = dynamicBuiltinNameMeaningsToTypes meanings
        typecheckConfig = TypeConfig True types mempty mempty Nothing
        typecheck = rename >=> typecheckTerm typecheckConfig
    _ <- runQuoteT $ typecheck term
    -- We do not rename terms before evaluating them, because the evaluator must work correctly over
    -- terms with duplicate names, because it produces such terms during evaluation.
    -- The bang is important in order to force the effects of a computation regardless of whether
    -- the result of the computation is forced or not.
    return $! evaluateCek meanings term
