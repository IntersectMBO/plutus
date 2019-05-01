module Data.Array.Extra
  ( move
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (fromMaybe)

move :: forall a. Show a => Int -> Int -> Array a -> Array a
move source destination before
 | destination == source = before
 | otherwise = fromMaybe before do
     x <- Array.index before source
     midway <- Array.deleteAt source before
     after <- Array.insertAt destination x midway
     pure after
