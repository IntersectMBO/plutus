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
import           Language.PlutusCore.Core
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty

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

feedEmitHandler
    :: DynamicBuiltinNameMeanings
    -> Term TyName Name ()
    -> EmitHandler r
    -> IO r
feedEmitHandler means term (EmitHandler handler) = handler means term

withEmitHandler :: AnEvaluator Term m r -> (EmitHandler (m r) -> IO r2) -> IO r2
withEmitHandler eval k = k . EmitHandler $ \env -> evaluate . eval env

withEmitTerm
    :: KnownType a
    => (Term TyName Name () -> EmitHandler r1 -> IO r2)
    -> EmitHandler r1
    -> IO ([a], r2)
withEmitTerm cont (EmitHandler handler) =
    withEmit $ \emit -> do
        counter <- nextGlobalUnique
        let dynEmitName = DynamicBuiltinName $ "emit" <> prettyText counter
            dynEmitTerm = dynamicCall dynEmitName
            dynEmitDef  = dynamicCallAssign dynEmitName emit
        cont dynEmitTerm . EmitHandler $ handler . insertDynamicBuiltinNameDefinition dynEmitDef

withEmitEvaluateBy
    :: KnownType a
    => AnEvaluator Term m b
    -> DynamicBuiltinNameMeanings
    -> (Term TyName Name () -> Term TyName Name ())
    -> IO ([a], m b)
withEmitEvaluateBy eval means toTerm =
    withEmitHandler eval . withEmitTerm $ feedEmitHandler means . toTerm
