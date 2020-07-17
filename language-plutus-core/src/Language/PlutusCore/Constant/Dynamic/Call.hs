-- | A dynamic built-in name that allows to call arbitrary 'IO' actions over
-- PLC values of a built-in types (including dynamic built-in types).

{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Language.PlutusCore.Constant.Dynamic.Call
    ( dynamicCallTypeScheme
    , dynamicCallAssign
    , dynamicCall
    ) where

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.Evaluation.Machine.ExMemory
import           Language.PlutusCore.Generators.Internal.Denotation
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe

import           Data.Proxy
import           System.IO.Unsafe

dynamicCallTypeScheme
    :: forall a uni term.
       (HasConstantIn uni term, KnownType term a, GShow uni, GEq uni, uni `Includes` ())
    => TypeScheme term '[a] ()
dynamicCallTypeScheme = Proxy `TypeSchemeArrow` TypeSchemeResult Proxy

dynamicCallAssign
    :: (HasConstantIn uni term, KnownType term a, GShow uni, GEq uni, uni `Includes` ())
    => DynamicBuiltinName
    -> (a -> IO ())
    -> (ExMemory -> ExBudget)
    -> DynamicBuiltinNameDefinition term
dynamicCallAssign name f exF =
    DynamicBuiltinNameDefinition name $
        DynamicBuiltinNameMeaning dynamicCallTypeScheme (unsafePerformIO . f) exF

dynamicCall
    :: forall ann a uni proxy.
       ( KnownType (Term TyName Name uni ann) a, FromConstant (Term TyName Name uni ann)
       , GShow uni, GEq uni, uni `Includes` ()
       )
    => proxy ann -> proxy a -> DynamicBuiltinName -> Term TyName Name uni ()
dynamicCall _ _ =
    embedDynamicBuiltinNameInTerm @(Term TyName Name _ ann) $ dynamicCallTypeScheme @a
