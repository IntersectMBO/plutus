-- | A dynamic built-in type test.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module DynamicBuiltins.Call
    ( dynamicCallAssign
    , dynamicCall
    , withEmitEvaluateCek
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           Language.PlutusCore.Interpreter.CekMachine

import           Control.Exception                          (evaluate)
import           Data.IORef
import           System.IO.Unsafe

dynamicCallAssign
    :: (forall size. TypedBuiltin size a)
    -> DynamicBuiltinName
    -> (a -> IO ())
    -> DynamicBuiltinNameDefinition
dynamicCallAssign tb name f =
    DynamicBuiltinNameDefinition name $ DynamicBuiltinNameMeaning sch sem where
        sch =
            TypeSchemeBuiltin tb `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 1) TypedBuiltinSizedSize)  -- Hacky-hacky.
        sem = unsafePerformIO . f

dynamicCall :: DynamicBuiltinName -> Term tyname name ()
dynamicCall = dynamicBuiltinNameAsTerm

withEmit :: ((a -> IO ()) -> IO b) -> IO ([a], b)
withEmit k = do
    xsVar <- newIORef id
    y <- k $ \x -> modifyIORef xsVar $ \ds -> ds . (x :)
    ds <- readIORef xsVar
    return (ds [], y)

withEmitEvaluateCek
    :: (forall size. TypedBuiltin size a)
    -> (Term TyName Name () -> Term TyName Name ())
    -> IO ([a], EvaluationResult)
withEmitEvaluateCek tb toTerm =
    withEmit $ \emit ->
        let name = DynamicBuiltinName "emit"
            env = insertDynamicBuiltinNameDefinition (dynamicCallAssign tb name emit) mempty
            in evaluate . evaluateCek env . toTerm $ dynamicCall name
