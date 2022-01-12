{-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}

module PlutusCore.Builtin.KnownKind where

import PlutusCore.Core

import Data.Kind as GHC
import GHC.Types
import Universe

-- | The type of singletonized Haskell kinds representing Plutus kinds.
-- Indexing by a Haskell kind allows us to avoid an 'error' call in the 'ToKind' instance of
-- 'DefaultUni' and not worry about proxies in the type of 'knownKind'.
data SingKind k where
    SingType      :: SingKind GHC.Type
    SingKindArrow :: SingKind k -> SingKind l -> SingKind (k -> l)

-- | For reifying Haskell kinds representing Plutus kinds at the term level.
class KnownKind k where
    knownKind :: SingKind k

-- | Plutus only supports lifted types, hence the equality constraint.
instance rep ~ LiftedRep => KnownKind (TYPE rep) where
    knownKind = SingType

instance (KnownKind dom, KnownKind cod) => KnownKind (dom -> cod) where
    knownKind = SingKindArrow (knownKind @dom) (knownKind @cod)

-- We need this for type checking Plutus, however we get Plutus types/terms/programs by either
-- producing them directly or by parsing/decoding them and in both the cases we have access to the
-- @Typeable@ information for the Haskell kind of a type and so we could just keep it around
-- (instead of throwing it away like we do now) and compute the Plutus kind directly from that.
-- That might be less efficient and probably requires updating the Plutus Tx compiler, so we went
-- with the simplest option for now and it's to have a class. Providing an instance per universe is
-- no big deal.
-- | For computing the Plutus kind of a built-in type. See 'kindOfBuiltinType'.
class ToKind (uni :: GHC.Type -> GHC.Type) where
    -- | Reify the kind of a type from the universe at the term level.
    toSingKind :: uni (Esc (a :: k)) -> SingKind k

-- | Convert a reified Haskell kind to a Plutus kind.
demoteKind :: SingKind k -> Kind ()
demoteKind SingType                = Type ()
demoteKind (SingKindArrow dom cod) = KindArrow () (demoteKind dom) (demoteKind cod)

-- | Compute the kind of a type from a universe.
kindOfBuiltinType :: ToKind uni => uni (Esc a) -> Kind ()
kindOfBuiltinType = demoteKind . toSingKind
