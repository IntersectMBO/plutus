{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Language.PlutusCore.Builtin.Common
    ( typecheckEvaluate
    , withEmit
    , withEmitEvaluateBy
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant
import           Language.PlutusCore.Pretty

import           Language.PlutusCore.Interpreter.CekMachine

import           Language.PlutusCore.Builtin.Call

import           Control.Exception                          (evaluate)
import           Control.Monad.Except
import           Data.IORef
import           System.IO.Unsafe                           (unsafePerformIO)

-- | Type check and evaluate a term that can contain dynamic built-ins.
-- Does not support nested dynamic built-in types, so do not use it for terms
-- that may caontain such types.
typecheckEvaluate
    :: (MonadError (Error ()) m, MonadQuote m)
    => DynamicBuiltinNameMeanings -> Term TyName Name () -> m EvaluationResult
typecheckEvaluate meanings term = do
    let types = dynamicBuiltinNameMeaningsToTypes meanings
        typecheckConfig = TypeCheckCfg 1000 $ TypeConfig True types
        typecheck = rename >=> annotateTerm >=> typecheckTerm typecheckConfig
    _ <- typecheck term
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

globalUniqueVar :: IORef Int
globalUniqueVar = unsafePerformIO $ newIORef 0
{-# NOINLINE globalUniqueVar #-}

nextGlobalUnique :: IO Int
nextGlobalUnique = atomicModifyIORef' globalUniqueVar $ \i -> (i, succ i)

withEmitEvaluateBy
    :: Evaluator Term
    -> (forall size. TypedBuiltin size a)
    -> (Term TyName Name () -> Term TyName Name ())
    -> IO ([a], EvaluationResult)
withEmitEvaluateBy eval tb toTerm =
    withEmit $ \emit -> do
        counter <- nextGlobalUnique
        let dynamicEmitName       = DynamicBuiltinName $ "emit" <> prettyText counter
            dynamicEmitTerm       = dynamicCall dynamicEmitName
            dynamicEmitDefinition = dynamicCallAssign tb dynamicEmitName emit
            env  = insertDynamicBuiltinNameDefinition dynamicEmitDefinition mempty
            term = toTerm dynamicEmitTerm
        evaluate $ eval env term
