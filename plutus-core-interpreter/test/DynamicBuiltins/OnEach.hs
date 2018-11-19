-- | A dynamic built-in type test.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}

module DynamicBuiltins.OnEach
    ( dynamicOnEachName
    , dynamicOnEachAssign
    , dynamicOnEach
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

import           System.IO.Unsafe

dynamicOnEachName :: DynamicBuiltinName
dynamicOnEachName = DynamicBuiltinName "onEach"

dynamicOnEachAssign
    :: (forall size. TypedBuiltin size a) -> (a -> IO ()) -> DynamicBuiltinNameDefinition
dynamicOnEachAssign tb f =
    DynamicBuiltinNameDefinition dynamicOnEachName $ DynamicBuiltinNameMeaning sch sem where
        sch =
            TypeSchemeBuiltin tb `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 1) TypedBuiltinSizedSize)  -- Hacky-hacky.
        sem = unsafePerformIO . f

dynamicOnEach :: Term tyname name ()
dynamicOnEach = dynamicBuiltinNameAsTerm dynamicOnEachName
