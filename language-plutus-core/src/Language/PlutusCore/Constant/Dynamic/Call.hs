-- | A dynamic built-in name that allows to call arbitrary 'IO' actions over
-- PLC values of a built-in types (including dynamic built-in types).

{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module Language.PlutusCore.Constant.Dynamic.Call
    ( dynamicCallAssign
    , dynamicCall
    ) where

import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Lexer.Type     hiding (name)
import           Language.PlutusCore.Type

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
