{-# LANGUAGE FlexibleInstances #-}

module PlutusCore.Value (
  Value (..),
  empty,
  fromList,
  toList,
  totalSize,
) where

import Codec.Serialise (Serialise)
import Control.DeepSeq (NFData)
import Data.Bifunctor
import Data.ByteString (ByteString)
import Data.ByteString.Base64 qualified as Base64
import Data.Hashable (Hashable)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text.Encoding qualified as Text

import PlutusPrelude (Pretty (..))

newtype Value = Value {unValue :: Map ByteString (Map ByteString Integer)}
  deriving newtype (Eq, Show, Hashable, Serialise, NFData)

empty :: Value
empty = Value mempty

toList :: Value -> [(ByteString, [(ByteString, Integer)])]
toList = Map.toList . Map.map Map.toList . unValue

fromList :: [(ByteString, [(ByteString, Integer)])] -> Value
fromList =
  normalize
    . Value
    . Map.fromListWith (Map.unionWith (+))
    . fmap (second (Map.fromListWith (+)))

normalize :: Value -> Value
normalize = Value . Map.filter Map.null . Map.map (Map.filter (== 0)) . unValue

totalSize :: Value -> Int
totalSize = Map.foldl' (\n -> (n +) .  Map.size) 0 . unValue

instance Pretty Value where
  pretty = pretty . fmap (bimap toText (fmap (first toText))) . toList
   where
    toText = Text.decodeLatin1 . Base64.encode
