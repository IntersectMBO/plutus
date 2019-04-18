{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module Language.PlutusCore.Constant.Dynamic.Emit
    ( withEmit
    , EmitHandler (..)
    , feedEmitHandler
    , withEmitHandler
    , withEmitTerm
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

-- This does not stream elements lazily. There is a version that allows to stream elements lazily,
-- but we do not have it here because it's way too convoluted.
-- See https://github.com/input-output-hk/plutus/pull/336 if you really need lazy streaming.
withEmit :: ((a -> IO ()) -> IO b) -> IO ([a], b)
withEmit k = do
    xsVar <- newIORef id
    y <- k $ \x -> modifyIORef xsVar $ \ds -> ds . (x :)
    ds <- readIORef xsVar
    return (ds [], y)

globalUniqueVar :: IORef Int
globalUniqueVar = unsafePerformIO $ newIORef 0
{-# NOINLINE globalUniqueVar #-}

nextGlobalUnique :: IO Int
nextGlobalUnique = atomicModifyIORef' globalUniqueVar $ \i -> (succ i, i)

newtype EmitHandler r = EmitHandler
    { unEmitHandler :: DynamicBuiltinNameMeanings -> Term TyName Name () -> IO r
    }

feedEmitHandler :: Term TyName Name () -> EmitHandler r -> IO r
feedEmitHandler term (EmitHandler handler) = handler mempty term

withEmitHandler :: Evaluator Term m -> (EmitHandler (m EvaluationResultDef) -> IO r2) -> IO r2
withEmitHandler eval k = k . EmitHandler $ \env -> evaluate . eval env

withEmitTerm
    :: TypedBuiltin a
    -> (Term TyName Name () -> EmitHandler r1 -> IO r2)
    -> EmitHandler r1
    -> IO ([a], r2)
withEmitTerm tb cont (EmitHandler handler) =
    withEmit $ \emit -> do
        counter <- nextGlobalUnique
        let dynEmitName = DynamicBuiltinName $ "emit" <> prettyText counter
            dynEmitTerm = dynamicCall dynEmitName
            dynEmitDef  = dynamicCallAssign tb dynEmitName emit
        cont dynEmitTerm . EmitHandler $ handler . insertDynamicBuiltinNameDefinition dynEmitDef

withEmitEvaluateBy
    :: Evaluator Term m
    -> TypedBuiltin a
    -> (Term TyName Name () -> Term TyName Name ())
    -> IO ([a], m EvaluationResultDef)
withEmitEvaluateBy eval tb toTerm =
    withEmitHandler eval . withEmitTerm tb $ feedEmitHandler . toTerm
