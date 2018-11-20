{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Language.PlutusCore.Builtin.Common
    ( typecheckEvaluateBy
    , withEmit
--     , withEmitTypecheckEvaluateBy
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Evaluation.Result

import           Language.PlutusCore.Interpreter.CekMachine

import           Language.PlutusCore.Builtin.Call

import           Control.Exception                          (evaluate)
import           Control.Monad.Except
import           Data.IORef

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckEvaluateBy
    :: (MonadError (Error ()) m) -- , MonadQuote m)
    => Evaluator Term -> DynamicBuiltinNameMeanings -> Term TyName Name () -> m EvaluationResult
typecheckEvaluateBy eval meanings term = -- do
    -- let types = dynamicBuiltinNameMeaningsToTypes meanings
    --     typecheckConfig = TypeCheckCfg 1000 $ TypeConfig True types
    --     typecheck = rename >=> annotateTerm >=> typecheckTerm typecheckConfig
    -- _ <- typecheck term
    -- We do not rename terms before evaluating them, because the evaluator must work correctly over
    -- terms with duplicate names, because it produces such terms during evaluation.
    return $ evaluateCek meanings term

withEmit :: ((a -> IO ()) -> IO b) -> IO ([a], b)
withEmit k = do
    xsVar <- newIORef id
    -- We may want to place 'unsafeInterleaveIO' here just to be lazy and cool.
    y <- k $ \x -> modifyIORef xsVar $ \ds -> ds . (x :)
    ds <- readIORef xsVar
    return (ds [], y)

-- withEmitTypecheckEvaluateBy
--     :: (forall size. TypedBuiltin size a)
--     -> Evaluator Term
--     -> (Term TyName Name () -> Term TyName Name ())
--     -> IO ([a], Either (Error ()) EvaluationResult)
-- withEmitTypecheckEvaluateBy eval tb toTerm =
--     withEmit $ \emit ->
--         let name = DynamicBuiltinName "emit"
--             -- env  = insertDynamicBuiltinNameDefinition (dynamicCallAssign tb name emit) mempty
--             term = toTerm $ dynamicCall name
--             in traverse evaluate . runQuote . runExceptT $ typecheckEvaluateBy eval env term
