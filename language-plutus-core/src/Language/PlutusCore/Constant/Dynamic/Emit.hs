{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Language.PlutusCore.Constant.Dynamic.Emit
    ( withEmit
    , EmitHandler
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
import           Data.Proxy
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

type EmitHandler uni r = DynamicBuiltinNameMeanings uni -> Term TyName Name uni () -> IO r

withEmitHandler :: AnEvaluator Term uni m r -> (EmitHandler uni (m r) -> IO r2) -> IO r2
withEmitHandler eval k = k $ \env -> evaluate . eval env

withEmitTerm
    :: forall a uni r1 r2.
       (KnownType uni a, GShow uni, GEq uni, uni `Includes` ())
    => (EmitHandler uni r1 -> Term TyName Name uni () -> IO r2)
    -> EmitHandler uni r1
    -> IO ([a], r2)
withEmitTerm cont handler =
    withEmit $ \emit -> do
        counter <- nextGlobalUnique
        let dynEmitName = DynamicBuiltinName $ "emit" <> display counter
            dynEmitTerm = dynamicCall (Proxy @a) dynEmitName
            dynEmitDef  = dynamicCallAssign dynEmitName emit (\_ -> ExBudget 1 1) -- TODO
        cont (handler . insertDynamicBuiltinNameDefinition dynEmitDef) dynEmitTerm

withEmitEvaluateBy
    :: (KnownType uni a, GShow uni, GEq uni, uni `Includes` ())
    => AnEvaluator Term uni m b
    -> DynamicBuiltinNameMeanings uni
    -> (Term TyName Name uni () -> Term TyName Name uni ())
    -> IO ([a], m b)
withEmitEvaluateBy eval means inst =
    withEmitHandler eval . withEmitTerm $ \handle -> handle means . inst
