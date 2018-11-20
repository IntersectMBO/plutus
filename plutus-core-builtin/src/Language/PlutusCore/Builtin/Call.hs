-- | A dynamic built-in name that allows to call arbitrary 'IO' actions over
-- PLC values of a built-in types (including dynamic built-in types).

{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module Language.PlutusCore.Builtin.Call
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
        sch = TypeSchemeBuiltin tb `TypeSchemeArrow` TypeSchemeBuiltin (TypedBuiltinDyn @())
        sem = unsafePerformIO . f

dynamicCall :: DynamicBuiltinName -> Term tyname name ()
dynamicCall = dynamicBuiltinNameAsTerm
