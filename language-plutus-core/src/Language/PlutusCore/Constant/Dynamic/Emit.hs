{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeOperators     #-}

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
import           Language.PlutusCore.Evaluation.Evaluator
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Universe

import           Control.Exception                                  (evaluate)
import           Data.IORef
import           System.IO.Unsafe                                   (unsafePerformIO)

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

newtype EmitHandler uni r = EmitHandler
    { unEmitHandler :: DynamicBuiltinNameMeanings uni -> Term TyName Name uni () -> IO r
    }

feedEmitHandler
    :: DynamicBuiltinNameMeanings uni
    -> Term TyName Name uni ()
    -> EmitHandler uni r
    -> IO r
feedEmitHandler means term (EmitHandler handler) = handler means term

withEmitHandler :: AnEvaluator Term uni m r -> (EmitHandler uni (m r) -> IO r2) -> IO r2
withEmitHandler eval k = k . EmitHandler $ \env -> evaluate . eval env

withEmitTerm
    :: (KnownType uni a, GShow uni, GEq uni, uni `Includes` ())
    => (Term TyName Name uni () -> EmitHandler uni r1 -> IO r2)
    -> EmitHandler uni r1
    -> IO ([a], r2)
withEmitTerm cont (EmitHandler handler) =
    withEmit $ \emit -> do
        counter <- nextGlobalUnique
        let dynEmitName = DynamicBuiltinName $ "emit" <> prettyText counter
            dynEmitTerm = dynamicCall dynEmitName
            dynEmitDef  = dynamicCallAssign dynEmitName emit (\_ -> ExBudget 1 1) -- TODO
        cont dynEmitTerm . EmitHandler $ handler . insertDynamicBuiltinNameDefinition dynEmitDef

withEmitEvaluateBy
    :: (KnownType uni a, GShow uni, GEq uni, uni `Includes` ())
    => AnEvaluator Term uni m b
    -> DynamicBuiltinNameMeanings uni
    -> (Term TyName Name uni () -> Term TyName Name uni ())
    -> IO ([a], m b)
withEmitEvaluateBy eval means inst =
    withEmitHandler eval . withEmitTerm $ feedEmitHandler means . inst
