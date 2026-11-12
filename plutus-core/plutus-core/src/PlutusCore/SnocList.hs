{-# LANGUAGE BangPatterns #-}

-- | Lists with a strict spine and strict elements, extended and inspected from the right.
module PlutusCore.SnocList
  ( SnocList (..)
  , fromList
  , toListWith
  , length
  ) where

import Data.List (foldl')
import Prelude hiding (length)

-- | 'Snoc' appends one element in constant time.
data SnocList a = SNil | Snoc !(SnocList a) !a
  deriving stock (Show)

-- | Build a snoc-list in source order.
fromList :: [a] -> SnocList a
fromList = foldl' Snoc SNil
{-# INLINE fromList #-}

-- | Map elements into an ordinary list in source order without an intermediate list.
toListWith :: (a -> b) -> SnocList a -> [b]
toListWith f = go []
  where
    go xs SNil = xs
    go xs (Snoc rest x) = go (f x : xs) rest
{-# INLINE toListWith #-}

-- | Count elements without inspecting their contents.
length :: SnocList a -> Int
length = go 0
  where
    go !n SNil = n
    go !n (Snoc rest _) = go (n + 1) rest
{-# INLINE length #-}
