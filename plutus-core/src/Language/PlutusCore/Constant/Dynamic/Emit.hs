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
import           Language.PlutusCore.Evaluation.Machine.ExMemory
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

newtype EmitHandler uni fun r = EmitHandler
    { unEmitHandler
        :: DynamicBuiltinNameMeanings (WithMemory Term uni fun) -> Plain Term uni fun -> IO r
    }

feedEmitHandler
    :: DynamicBuiltinNameMeanings (WithMemory Term uni fun)
    -> Plain Term uni fun
    -> EmitHandler uni fun r
    -> IO r
feedEmitHandler means term (EmitHandler handler) = handler means term

withEmitHandler :: AnEvaluator Term uni fun m r -> (EmitHandler uni fun (m r) -> IO r2) -> IO r2
withEmitHandler eval k = k . EmitHandler $ \env -> evaluate . eval env

withEmitTerm
    :: ( KnownType (WithMemory Term uni fun) a, GShow uni, GEq uni, uni `Includes` ()
       , Closed uni, uni `Everywhere` ExMemoryUsage
       )
    => (Plain Term uni fun -> EmitHandler uni fun r1 -> IO r2)
    -> EmitHandler uni fun r1
    -> IO ([a], r2)
withEmitTerm cont (EmitHandler handler) =
    withEmit $ \emit -> do
        counter <- nextGlobalUnique
        let dynEmitName = DynamicBuiltinName $ "emit" <> display counter
            dynEmitTerm = dynamicCall dynEmitName
            dynEmitDef  = dynamicCallAssign dynEmitName emit (\_ -> ExBudget 1 1) -- TODO
        cont dynEmitTerm . EmitHandler $ handler . insertDynamicBuiltinNameDefinition dynEmitDef

withEmitEvaluateBy
    :: ( KnownType (WithMemory Term uni fun) a, GShow uni, GEq uni, uni `Includes` ()
       , Closed uni, uni `Everywhere` ExMemoryUsage
       )
    => AnEvaluator Term uni fun m b
    -> DynamicBuiltinNameMeanings (WithMemory Term uni fun)
    -> (Term TyName Name uni fun () -> Term TyName Name uni fun ())
    -> IO ([a], m b)
withEmitEvaluateBy eval means inst =
    withEmitHandler eval . withEmitTerm $ feedEmitHandler means . inst
