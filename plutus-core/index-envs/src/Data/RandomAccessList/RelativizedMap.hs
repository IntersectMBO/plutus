{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.RandomAccessList.RelativizedMap (RelativizedMap (..)) where

import Data.Word

import Data.RandomAccessList.Class qualified as RAL

import Data.IntMap.Strict qualified as IM
import GHC.Exts (IsList)

{-| A sequence implemented by a map from "levels" to values and a counter giving the "current"
level. -}
data RelativizedMap a = RelativizedMap (IM.IntMap a) {-# UNPACK #-} !Word64
  deriving stock (Show, Eq)
  deriving (IsList) via RAL.AsRAL (RelativizedMap a)

instance RAL.RandomAccessList (RelativizedMap a) where
  type Element (RelativizedMap a) = a

  {-# INLINEABLE empty #-}
  empty = RelativizedMap mempty 0
  {-# INLINEABLE cons #-}
  cons a (RelativizedMap im l) = RelativizedMap (IM.insert (fromIntegral l) a im) (l + 1)
  {-# INLINEABLE uncons #-}
  uncons (RelativizedMap _ 0) = Nothing
  uncons (RelativizedMap im l) = case IM.maxViewWithKey im of
    Nothing -> Nothing
    Just ((_, a), res) -> Just (a, RelativizedMap res (l - 1))
  {-# INLINEABLE length #-}
  length (RelativizedMap _ l) = l
  {-# INLINEABLE indexZero #-}
  indexZero (RelativizedMap _ 0) _ = Nothing
  indexZero (RelativizedMap im l) w =
    let maxIndex = l - 1
     in if w > maxIndex then Nothing else IM.lookup (fromIntegral maxIndex - fromIntegral w) im
