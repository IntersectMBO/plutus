{-# LANGUAGE FlexibleContexts #-}

module DynamicBuiltins.Common
    ( typecheckEvaluate
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Language.PlutusCore.Interpreter.CekMachine

import           Control.Monad.Except

-- | Type check and evaluate a term that can contain dynamic built-ins.
-- Does not support nested dynamic built-in types, so do not use it for terms
-- that may contain such types.
typecheckEvaluate
    :: (MonadError (Error ()) m, MonadQuote m)
    => DynamicBuiltinNameMeanings -> Term TyName Name () -> m EvaluationResult
typecheckEvaluate meanings term = do
    let types = dynamicBuiltinNameMeaningsToTypes meanings
<<<<<<< HEAD
    _ <- annotateTerm term >>= typecheckTerm (TypeConfig True types Nothing)
=======
        typecheckConfig = TypeCheckCfg 1000 $ TypeConfig True types
        typecheck = rename >=> annotateTerm >=> typecheckTerm typecheckConfig
    _ <- typecheck term
    -- We do not rename terms before evaluating them, because the evaluator must work correctly over
    -- terms with duplicate names, because it produces such terms during evaluation.
>>>>>>> bdfa2cce876b3fe04e75dade973b663804428d18
    return $ evaluateCek meanings term
