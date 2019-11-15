module Data.Array.Extra
  ( move
  , intersperse
  , lookup
  ) where

import Prelude
import Data.Tuple.Nested (type (/\))
import Data.Array (snoc, foldl)
import Data.Array as Array
import Data.Maybe (Maybe, fromMaybe)
import Data.Tuple (fst, snd)

move :: forall a. Int -> Int -> Array a -> Array a
move source destination before
  | destination == source = before
  | otherwise =
    fromMaybe before do
      x <- Array.index before source
      midway <- Array.deleteAt source before
      after <- Array.insertAt destination x midway
      pure after

intersperse :: forall a. a -> Array a -> Array a
intersperse sep = foldl reducer []
  where
  reducer [] x = [ x ]

  reducer acc x = snoc (snoc acc sep) x

lookup :: forall k v. Eq k => k -> Array (k /\ v) -> Maybe v
lookup key = map snd <<< Array.find (fst >>> (==) key)
