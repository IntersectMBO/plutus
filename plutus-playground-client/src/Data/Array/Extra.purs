module Data.Array.Extra
  ( move
  , intersperse
  ) where

import Prelude

import Data.Array (snoc, foldl)
import Data.Array as Array
import Data.Maybe (fromMaybe)

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
