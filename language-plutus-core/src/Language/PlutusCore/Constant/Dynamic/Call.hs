-- | A dynamic built-in name that allows to call arbitrary 'IO' actions over
-- PLC values of a built-in types (including dynamic built-in types).

module Language.PlutusCore.Constant.Dynamic.Call
    ( dynamicCallTypeScheme
    , dynamicCallAssign
    , dynamicCall
    ) where

import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Lexer.Type     hiding (name)
import           Language.PlutusCore.Type

import           Data.Proxy
import           System.IO.Unsafe

dynamicCallTypeScheme :: KnownType a => TypeScheme (a -> ()) ()
dynamicCallTypeScheme = Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

dynamicCallAssign
    :: KnownType a
    => DynamicBuiltinName
    -> (a -> IO ())
    -> DynamicBuiltinNameDefinition
dynamicCallAssign name f =
    DynamicBuiltinNameDefinition name $
        DynamicBuiltinNameMeaning dynamicCallTypeScheme (unsafePerformIO . f)

dynamicCall :: DynamicBuiltinName -> Term tyname name ()
dynamicCall = dynamicBuiltinNameAsTerm
