-- | A dynamic built-in type test.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module DynamicBuiltins.Call
    ( dynamicCallName
    , dynamicCallAssign
    , dynamicCall
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           System.IO.Unsafe

dynamicCallName :: DynamicBuiltinName
dynamicCallName = DynamicBuiltinName "onEach"

dynamicCallAssign
    :: (forall size. TypedBuiltin size a) -> (a -> IO ()) -> DynamicBuiltinNameDefinition
dynamicCallAssign tb f =
    DynamicBuiltinNameDefinition dynamicCallName $ DynamicBuiltinNameMeaning sch sem where
        sch =
            TypeSchemeBuiltin tb `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 1) TypedBuiltinSizedSize)  -- Hacky-hacky.
        sem = unsafePerformIO . f

dynamicCall :: Term tyname name ()
dynamicCall = dynamicBuiltinNameAsTerm dynamicCallName
