{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Language.PlutusCore.Constant.Dynamic.Emit
    ( withEmit
    , withEmitEvaluateBy
    ) where

import           Language.PlutusCore.Constant.Dynamic.Call
import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Evaluation.Result
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Type

import           Control.Exception                         (evaluate)
import           Data.IORef
import           System.IO.Unsafe                          (unsafePerformIO)

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

-- We do not type check terms here, because type checking of nested dynamic built-in types simply
-- does not work. The type checker can't be quickly repaired, so we keep it like this for now.
withEmitEvaluateBy
    :: Evaluator Term m
    -> (forall size. TypedBuiltin size a)
    -> (Term TyName Name () -> Term TyName Name ())
    -> IO ([a], m EvaluationResult)
withEmitEvaluateBy eval tb toTerm =
    withEmit $ \emit -> do
        counter <- nextGlobalUnique
        let dynamicEmitName       = DynamicBuiltinName $ "emit" <> prettyText counter
            dynamicEmitTerm       = dynamicCall dynamicEmitName
            dynamicEmitDefinition = dynamicCallAssign tb dynamicEmitName emit
            env  = insertDynamicBuiltinNameDefinition dynamicEmitDefinition mempty
            term = toTerm dynamicEmitTerm
        evaluate $ eval env term
