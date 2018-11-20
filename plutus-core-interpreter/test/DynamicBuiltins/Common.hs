{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module DynamicBuiltins.Common
    ( typecheckEvaluate
    , withEmitTypecheckEvaluate
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Language.PlutusCore.Interpreter.CekMachine

import           DynamicBuiltins.Call

import           Control.Exception                          (evaluate)
import           Control.Monad.Except
import           Data.IORef

-- | Type check and evaluate a term that can contain dynamic built-ins.
typecheckEvaluate
    :: (MonadError (Error ()) m, MonadQuote m)
    => DynamicBuiltinNameMeanings -> Term TyName Name () -> m EvaluationResult
typecheckEvaluate meanings term = do
    let types = dynamicBuiltinNameMeaningsToTypes meanings
    _ <- annotateTerm term >>= typecheckTerm (TypeCheckCfg 1000 $ TypeConfig True types)
    return $ evaluateCek meanings term

withEmit :: ((a -> IO ()) -> IO b) -> IO ([a], b)
withEmit k = do
    xsVar <- newIORef id
    -- We may want to place 'unsafeInterleaveIO' here just to be lazy and cool.
    y <- k $ \x -> modifyIORef xsVar $ \ds -> ds . (x :)
    ds <- readIORef xsVar
    return (ds [], y)

withEmitTypecheckEvaluate
    :: (forall size. TypedBuiltin size a)
    -> (Term TyName Name () -> Term TyName Name ())
    -> IO ([a], Either (Error ()) EvaluationResult)
withEmitTypecheckEvaluate tb toTerm =
    withEmit $ \emit ->
        let name = DynamicBuiltinName "emit"
            env  = insertDynamicBuiltinNameDefinition (dynamicCallAssign tb name emit) mempty
            term = toTerm $ dynamicCall name
            in traverse evaluate . runQuote . runExceptT $ typecheckEvaluate env term
