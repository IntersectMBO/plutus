{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Vector.Orphans () where

import Data.Hashable (Hashable (hashWithSalt))
import Data.Vector.Strict qualified as Strict
import Flat (Flat (..))
import Flat.Instances.Vector ()

instance (Hashable a) => Hashable (Strict.Vector a) where
  hashWithSalt = Strict.foldl' hashWithSalt

instance (Flat a) => Flat (Strict.Vector a) where
  size = size . Strict.toLazy -- Strict to Lazy is O(1)
  encode = encode . Strict.toLazy
  decode = Strict.fromLazy <$> decode -- Strict from Lazy is O(1)
