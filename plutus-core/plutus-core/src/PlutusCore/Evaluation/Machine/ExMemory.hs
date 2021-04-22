{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MagicHash             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module PlutusCore.Evaluation.Machine.ExMemory
( ExMemory(..)
, ExCPU(..)
, GenericExMemoryUsage(..)
, ExMemoryUsage(..)
) where

import           PlutusCore.Core
import           PlutusCore.Name
import           PlutusCore.Pretty
import           PlutusCore.Universe
import           PlutusPrelude

import           Control.Monad.RWS.Strict
import qualified Data.ByteString          as BS
import           Data.Proxy
import qualified Data.Text                as T
import           GHC.Generics
import           GHC.Integer
import           GHC.Integer.Logarithms
import           GHC.Prim

{- Note [Memory Usage for Plutus]

The base unit is 'ExMemory', which corresponds to machine words. For primitives,
we use static values for the size, see the corresponding instances. For
composite data types, the Generic instance is used, + 1 for the constructor tag.
For ADTs, the currently selected branch is counted, not the maximum value.
Memory usage of the annotation is not counted, because this should be
abstractly specifiable. It's an implementation detail.

-}

-- | Counts size in machine words (64bit for the near future)
newtype ExMemory = ExMemory Integer
  deriving (Eq, Ord, Show)
  deriving newtype (Num, Pretty, NFData)
  deriving (Semigroup, Monoid) via (Sum Integer)
deriving newtype instance PrettyDefaultBy config Integer => PrettyBy config ExMemory

-- TODO: 'Integer's are not particularly fast. Should we use @Int64@?
-- | Counts CPU units - no fixed base, proportional.
newtype ExCPU = ExCPU Integer
  deriving (Eq, Ord, Show)
  deriving newtype (Num, Pretty, NFData)
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

deriving via (GenericExMemoryUsage (Either a b)) instance
    (ExMemoryUsage a, ExMemoryUsage b) => ExMemoryUsage (Either a b)
deriving via (GenericExMemoryUsage (a, b)) instance
    (ExMemoryUsage a, ExMemoryUsage b) => ExMemoryUsage (a, b)

deriving via (GenericExMemoryUsage Name) instance ExMemoryUsage Name
deriving via (GenericExMemoryUsage (Type tyname uni ann)) instance
    (ExMemoryUsage tyname, ExMemoryUsage ann) => ExMemoryUsage (Type tyname uni ann)
deriving via (GenericExMemoryUsage (Kind ann)) instance ExMemoryUsage ann => ExMemoryUsage (Kind ann)
deriving via (GenericExMemoryUsage (Term tyname name uni fun ann)) instance
    ( ExMemoryUsage tyname, ExMemoryUsage name, ExMemoryUsage ann
    , Closed uni, uni `Everywhere` ExMemoryUsage, ExMemoryUsage fun
    ) => ExMemoryUsage (Term tyname name uni fun ann)
deriving newtype instance ExMemoryUsage TyName
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
  memoryUsage i = ExMemory (1 + smallInteger (integerLog2# (abs i) `quotInt#` integerToInt 64)) -- assume 64bit size

instance ExMemoryUsage BS.ByteString where
  memoryUsage bs = ExMemory $ (toInteger $ BS.length bs) `div` 8

instance ExMemoryUsage T.Text where
  memoryUsage text = memoryUsage $ T.unpack text -- TODO not accurate, as Text uses UTF-16

instance ExMemoryUsage Int where
  memoryUsage _ = 1

instance ExMemoryUsage Char where
  memoryUsage _ = 1

instance ExMemoryUsage Bool where
  memoryUsage _ = 1

deriving via GenericExMemoryUsage [a] instance ExMemoryUsage a => ExMemoryUsage [a]
