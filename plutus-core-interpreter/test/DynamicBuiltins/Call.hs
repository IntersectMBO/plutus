-- | A dynamic built-in name that allows to call arbitrary 'IO' actions over
-- PLC values of a built-in types (including dynamic built-in types).

{-# LANGUAGE RankNTypes #-}

module DynamicBuiltins.Call
    ( dynamicCallAssign
    , dynamicCall
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.Constant

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
            -- @TypedBuiltinUnit@ should be added and this should be removed.
            TypeSchemeBuiltin (TypedBuiltinSized (SizeValue 1) TypedBuiltinSizedSize)
        sem = unsafePerformIO . f

dynamicCall :: DynamicBuiltinName -> Term tyname name ()
dynamicCall = dynamicBuiltinNameAsTerm
