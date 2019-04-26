-- | A dynamic built-in name that allows to call arbitrary 'IO' actions over
-- PLC values of a built-in types (including dynamic built-in types).

{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module Language.PlutusCore.Constant.Dynamic.Call
    ( dynamicCallAssign
    , dynamicCallTypeScheme
    , dynamicCall
    ) where

import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Lexer.Type     hiding (name)
import           Language.PlutusCore.Type

import           System.IO.Unsafe

dynamicCallAssign
    :: TypedBuiltin a
    -> DynamicBuiltinName
    -> (a -> IO ())
    -> DynamicBuiltinNameDefinition
dynamicCallAssign tb name f =
    DynamicBuiltinNameDefinition name $ DynamicBuiltinNameMeaning sch sem where
        sch = dynamicCallTypeScheme tb
        sem = unsafePerformIO . f

dynamicCallTypeScheme :: TypedBuiltin a -> TypeScheme (a -> ()) ()
dynamicCallTypeScheme tb = TypeSchemeBuiltin tb `TypeSchemeArrow` TypeSchemeBuiltin (TypedBuiltinDyn @())

dynamicCall :: DynamicBuiltinName -> Term tyname name ()
dynamicCall = dynamicBuiltinNameAsTerm
