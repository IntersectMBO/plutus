-- | A dynamic built-in name that allows to call arbitrary 'IO' actions over
-- PLC values of a built-in types (including dynamic built-in types).

{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Language.PlutusCore.Constant.Dynamic.Call
    ( dynamicCallTypeScheme
    , dynamicCallAssign
    , dynamicCall
    ) where

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Universe

import           Data.Proxy
import           System.IO.Unsafe

dynamicCallTypeScheme
    :: (KnownType uni a, GShow uni, GEq uni, uni `Includes` Integer)
    => TypeScheme uni '[a] ()
dynamicCallTypeScheme = Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

dynamicCallAssign
    :: (KnownType uni a, GShow uni, GEq uni, uni `Includes` Integer)
    => DynamicBuiltinName
    -> (a -> IO ())
    -> (a -> ExBudget)
    -> DynamicBuiltinNameDefinition uni
dynamicCallAssign name f exF =
    DynamicBuiltinNameDefinition name $
        DynamicBuiltinNameMeaning dynamicCallTypeScheme (unsafePerformIO . f) exF

dynamicCall :: DynamicBuiltinName -> Term tyname name uni ()
dynamicCall = dynamicBuiltinNameAsTerm
