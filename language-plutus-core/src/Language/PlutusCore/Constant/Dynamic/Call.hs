-- | A dynamic built-in name that allows to call arbitrary 'IO' actions over
-- PLC values of a built-in types (including dynamic built-in types).

module Language.PlutusCore.Constant.Dynamic.Call
    ( dynamicCallTypeScheme
    , dynamicCallAssign
    , dynamicCall
    ) where

import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting

import           Data.Proxy
import           System.IO.Unsafe

dynamicCallTypeScheme :: KnownType a => TypeScheme (a -> ()) (a -> ExBudget) ()
dynamicCallTypeScheme = Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

dynamicCallAssign
    :: KnownType a
    => DynamicBuiltinName
    -> (a -> IO ())
    -> (a -> ExBudget) -- TODO do we actually need IO here?
    -> DynamicBuiltinNameDefinition
dynamicCallAssign name f exF =
    DynamicBuiltinNameDefinition name $
        DynamicBuiltinNameMeaning dynamicCallTypeScheme (unsafePerformIO . f) exF

dynamicCall :: DynamicBuiltinName -> Term tyname name ()
dynamicCall = dynamicBuiltinNameAsTerm
