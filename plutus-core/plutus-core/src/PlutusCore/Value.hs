{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ViewPatterns      #-}

module PlutusCore.Value (
  Value, -- Do not expose data constructor
  NestedMap,
  unpack,
  pack,
  empty,
  fromList,
  toList,
  totalSize,
  maxInnerSize,
) where

import Codec.Serialise (Serialise)
import Control.DeepSeq (NFData)
import Data.Bifunctor
import Data.ByteString (ByteString)
import Data.ByteString.Base64 qualified as Base64
import Data.Hashable (Hashable)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text.Encoding qualified as Text
import GHC.Generics

import PlutusPrelude (Pretty (..))

type NestedMap = Map ByteString (Map ByteString Integer)

-- | The underlying type of the UPLC built-in type @Value@.
data Value
  = Value
      !NestedMap
      {- ^ Map from (currency symbol, token name) to amount.

      Invariants: no empty inner map, and no zero amount.
      -}
      !(IntMap Int)
      {- ^ Map from size to the number of inner maps that have that size,
      useful for efficient retrieval of the size of the largest inner map.

      Invariant: all values are positive.
      -}
      {-# UNPACK #-} !Int
      -- ^ Total size, i.e., sum total of inner map sizes
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable, Serialise, NFData)

{-| Unpack a `Value` into a map from (currency symbol, token name) to amount.

The map is guaranteed to not contain empty inner map or zero amount.
-}
unpack :: Value -> NestedMap
unpack (Value v _ _) = v

{-| Pack a map from (currency symbol, token name) to amount into a `Value`.

The map will be filtered so that it does not contain empty inner map or zero amount.
-}
pack :: NestedMap -> Value
pack (normalize -> v) = Value v sizes size
 where
  sizes = Map.foldr' (IntMap.alter (maybe (Just 1) (Just . (+ 1))) . Map.size) mempty v
  size = Map.foldr' ((+) . Map.size) 0 v

{-| Total size, i.e., the number of distinct `(currency symbol, token name)` pairs
contained in the `Value`.
-}
totalSize :: Value -> Int
totalSize (Value _ _ size) = size

-- | Size of the largest inner map.
maxInnerSize :: Value -> Int
maxInnerSize (Value _ sizes _) = maybe 0 fst (IntMap.lookupMax sizes)

empty :: Value
empty = Value mempty mempty 0

toList :: Value -> [(ByteString, [(ByteString, Integer)])]
toList = Map.toList . Map.map Map.toList . unpack

fromList :: [(ByteString, [(ByteString, Integer)])] -> Value
fromList =
  pack
    . Map.fromListWith (Map.unionWith (+))
    . fmap (second (Map.fromListWith (+)))

normalize :: NestedMap -> NestedMap
normalize = Map.filter (not . Map.null) . Map.map (Map.filter (/= 0))

instance Pretty Value where
  pretty = pretty . fmap (bimap toText (fmap (first toText))) . toList
   where
    toText = Text.decodeLatin1 . Base64.encode
