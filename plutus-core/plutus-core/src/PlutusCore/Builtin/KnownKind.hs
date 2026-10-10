{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}

module PlutusCore.Builtin.KnownKind where

import PlutusCore.Core

import Data.Kind as GHC
import GHC.Types
import Universe

-- | Reify a Haskell kind as a Plutus kind.
class KnownKind (k :: GHC.Type) where
  knownKind :: Kind ()

-- | Plutus only supports lifted types, hence the equality constraint.
instance rep ~ LiftedRep => KnownKind (TYPE rep) where
  knownKind = Type ()

instance (KnownKind dom, KnownKind cod) => KnownKind (dom -> cod) where
  knownKind = KindArrow () (knownKind @dom) (knownKind @cod)

-- | Compute the Plutus kind of a bare built-in type head.
class ToKind (uni :: GHC.Type -> GHC.Type) where
  kindOfBuiltinType :: SomeTypeHead uni -> Kind ()
