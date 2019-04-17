module Data.String.Extra
       ( abbreviate
       , toHex
       , leftPadTo
       , repeat
       ) where

import Data.Array (intercalate)
import Data.Char as Char
import Data.Int as Int
import Data.Monoid (class Monoid, mempty)
import Data.String as String
import Prelude (map, max, (-), (<=), (<>), (>>>))

abbreviate :: String -> String
abbreviate str =
  if String.length str <= 7
  then str
  else String.take 7 str <> "..."

toHex :: String -> String
toHex =
  String.toCharArray
  >>> map (Char.toCharCode
           >>> Int.toStringAs Int.hexadecimal
           >>> leftPadTo 2 " ")
  >>> intercalate ""

leftPadTo :: Int -> String -> String -> String
leftPadTo length prefix str =
  repeat (max 0 (length - strlen)) prefix <> str
  where
    strlen = String.length str

repeat :: forall m. Monoid m => Int -> m -> m
repeat 0 str = mempty
repeat n str = str <> repeat (n - 1) str
