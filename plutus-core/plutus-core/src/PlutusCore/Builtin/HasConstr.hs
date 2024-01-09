{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module PlutusCore.Builtin.HasConstr
    ( ToConstr (..)
    ) where

import PlutusCore.Builtin.KnownTypeAst
import PlutusCore.Builtin.Polymorphism
import PlutusCore.Core
import PlutusCore.Name

import Data.Proxy
import Data.Word

class ToConstr term where
    toConstr
        :: forall rep. KnownTypeAst TyName (UniOf term) rep
        => Word64 -> [term] -> Opaque term rep

instance ToConstr (Term TyName name uni fun ()) where
    toConstr
        :: forall rep. KnownTypeAst TyName uni rep
        => Word64 -> [Term TyName name uni fun ()] -> Opaque (Term TyName name uni fun ()) rep
    toConstr ix = Opaque . Constr () (toTypeAst $ Proxy @rep) ix
