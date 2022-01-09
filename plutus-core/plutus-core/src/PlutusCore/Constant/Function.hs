{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.Constant.Function
    ( typeSchemeToType
    ) where

import PlutusCore.Constant.Kinded
import PlutusCore.Constant.Typed
import PlutusCore.Core
import PlutusCore.Name

import Data.Proxy
import Data.Text qualified as Text
import GHC.TypeLits

-- | Convert a 'TypeScheme' to the corresponding 'Type'.
-- Basically, a map from the PHOAS representation to the FOAS one.
typeSchemeToType :: TypeScheme term args res -> Type TyName (UniOf term) ()
typeSchemeToType sch@TypeSchemeResult       = toTypeAst sch
typeSchemeToType sch@(TypeSchemeArrow schB) =
    TyFun () (toTypeAst $ argOf sch) $ typeSchemeToType schB
typeSchemeToType (TypeSchemeAll proxy schK) = case proxy of
    (_ :: Proxy '(text, uniq, kind)) ->
        let text = Text.pack $ symbolVal @text Proxy
            uniq = fromIntegral $ natVal @uniq Proxy
            a    = TyName $ Name text $ Unique uniq
        in TyForall () a (runSingKind $ knownKind @kind) $ typeSchemeToType schK
