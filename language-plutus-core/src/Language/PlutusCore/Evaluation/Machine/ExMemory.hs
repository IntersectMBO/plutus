{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Evaluation.Machine.ExMemory
( Plain
, WithMemory
, ExMemory(..)
, ExCPU(..)
, GenericExMemoryUsage(..)
, ExMemoryUsage(..)
, withMemory
) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Name
import           Language.PlutusCore.Universe
import           PlutusPrelude

import           Control.Monad.RWS.Strict
import qualified Data.ByteString.Lazy         as BSL
import qualified Data.Kind                    as GHC
import           Data.Proxy
import qualified Data.Text                    as T
import           Foreign.Storable
import           GHC.Generics

{- Note [Memory Usage for Plutus]

The base unit is 'ExMemory', which corresponds to machine words. For primities,
we use static values for the size, see the corresponding instances. For
composite data types, the Generic instance is used, + 1 for the constructor tag.
For ADTs, the currently selected branch is counted, not the maximum value.
Memory usage of the annotation is not counted, because this should be
abstractily specifiable. It's an implementation detail.

-}

type Plain f (uni :: GHC.Type -> GHC.Type) = f TyName Name uni ()
-- | Caches Memory usage for builtin costing
type WithMemory f (uni :: GHC.Type -> GHC.Type) = f TyName Name uni ExMemory

-- | Counts size in machine words (64bit for the near future)
newtype ExMemory = ExMemory Integer
  deriving (Eq, Ord, Show)
  deriving newtype (Num, NFData)
  deriving (Semigroup, Monoid) via (Sum Integer)
-- You have to use a standalone declaration for deriving a 'PrettyBy' instance.
-- Yes, I also hate that.
deriving newtype instance PrettyDefaultBy config Integer => PrettyBy config ExMemory

-- | Counts CPU units - no fixed base, proportional.
newtype ExCPU = ExCPU Integer
  deriving (Eq, Ord, Show)
  deriving newtype (Num, NFData)
  deriving (Semigroup, Monoid) via (Sum Integer)
deriving newtype instance PrettyDefaultBy config Integer => PrettyBy config ExCPU

-- Based on https://github.com/ekmett/semigroups/blob/master/src/Data/Semigroup/Generic.hs
class GExMemoryUsage f where
  gmemoryUsage' :: f a -> ExMemory

gmemoryUsage :: (Generic a, GExMemoryUsage (Rep a)) => a -> ExMemory
gmemoryUsage x = gmemoryUsage' (from x)

instance GExMemoryUsage U1 where
  gmemoryUsage' _ = 1 -- No constructor

instance GExMemoryUsage V1 where
  gmemoryUsage' _ = 1 -- Empty datatype

instance ExMemoryUsage a => GExMemoryUsage (K1 i a) where
  gmemoryUsage' (K1 x) = memoryUsage x

instance GExMemoryUsage f => GExMemoryUsage (M1 i c f) where
  gmemoryUsage' (M1 x) = gmemoryUsage' x

instance (GExMemoryUsage f, GExMemoryUsage g) => GExMemoryUsage (f :*: g) where
  gmemoryUsage' (x1 :*: x2) = gmemoryUsage' x1 + gmemoryUsage' x2

instance (GExMemoryUsage f, GExMemoryUsage g) => GExMemoryUsage (f :+: g) where
  gmemoryUsage' (L1 x) = gmemoryUsage' x
  gmemoryUsage' (R1 x) = gmemoryUsage' x

newtype GenericExMemoryUsage a = GenericExMemoryUsage { getGenericExMemoryUsage :: a }
instance (Generic a, GExMemoryUsage (Rep a)) => ExMemoryUsage (GenericExMemoryUsage a) where
  memoryUsage (GenericExMemoryUsage x) = gmemoryUsage x

class ExMemoryUsage a where
    memoryUsage :: a -> ExMemory -- ^ How much memory does 'a' use?

deriving via (GenericExMemoryUsage (Name ann)) instance ExMemoryUsage ann => ExMemoryUsage (Name ann)
deriving via (GenericExMemoryUsage (Type TyName uni ann)) instance ExMemoryUsage ann => ExMemoryUsage (Type TyName uni ann)
deriving via (GenericExMemoryUsage (Builtin ann)) instance ExMemoryUsage ann => ExMemoryUsage (Builtin ann)
deriving via (GenericExMemoryUsage (Kind ann)) instance ExMemoryUsage ann => ExMemoryUsage (Kind ann)
deriving via (GenericExMemoryUsage BuiltinName) instance ExMemoryUsage BuiltinName
deriving via (GenericExMemoryUsage DynamicBuiltinName) instance ExMemoryUsage DynamicBuiltinName
deriving via (GenericExMemoryUsage (Term TyName Name uni ann))
  instance (ExMemoryUsage ann, Closed uni, uni `Everywhere` ExMemoryUsage) =>
    ExMemoryUsage (Term TyName Name uni ann)
deriving newtype instance ExMemoryUsage ann => ExMemoryUsage (TyName ann)
deriving newtype instance ExMemoryUsage ExMemory
deriving newtype instance ExMemoryUsage Unique

-- See https://github.com/input-output-hk/plutus/issues/1861
instance ExMemoryUsage (Some (TypeIn uni)) where
  memoryUsage _ = 1 -- TODO things like @list (list (list integer))@ take up a non-constant amount of space.

-- See https://github.com/input-output-hk/plutus/issues/1861
instance (Closed uni, uni `Everywhere` ExMemoryUsage) => ExMemoryUsage (Some (ValueOf uni)) where
  -- TODO this is just to match up with existing golden tests. We probably need to account for @uni@ as well.
  memoryUsage (Some (ValueOf uni x)) = bring (Proxy @ExMemoryUsage) uni (memoryUsage x)

instance ExMemoryUsage () where
  memoryUsage _ = 0 -- TODO or 1?

instance ExMemoryUsage Integer where
  memoryUsage _ = 2 -- TODO

instance ExMemoryUsage BSL.ByteString where
  memoryUsage bsl = ExMemory $ toInteger $ BSL.length bsl

instance ExMemoryUsage T.Text where
  memoryUsage text = memoryUsage $ T.unpack text -- TODO not accurate, as Text uses UTF-16

instance ExMemoryUsage Int where
  memoryUsage _ = 1

instance ExMemoryUsage Char where
  memoryUsage _ = 1

instance ExMemoryUsage Bool where
  memoryUsage _ = 1

instance ExMemoryUsage String where
  memoryUsage string = ExMemory $ toInteger $ sum $ fmap sizeOf string

withMemory :: ExMemoryUsage (f a) => Functor f => f a -> f ExMemory
withMemory x = fmap (const (memoryUsage x)) x
