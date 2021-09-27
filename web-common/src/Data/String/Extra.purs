module Data.String.Extra where

import Prologue
import Data.Array (intercalate)
import Data.Char as Char
import Data.Int as Int
import Data.Maybe (isJust)
import Data.String as String
import Data.String.CodeUnits as CodeUnits

abbreviate :: Int -> String -> String
abbreviate n str =
  let
    prefix = String.take n str
  in
    if str == prefix then
      str
    else
      prefix <> "..."

toHex :: String -> String
toHex =
  CodeUnits.toCharArray
    >>> map
        ( Char.toCharCode
            >>> Int.toStringAs Int.hexadecimal
            >>> leftPadTo 2 " "
        )
    >>> intercalate ""

leftPadTo :: Int -> String -> String -> String
leftPadTo length prefix str = repeat (max 0 (length - strlen)) prefix <> str
  where
  strlen = String.length str

rightPadTo :: Int -> String -> String -> String
rightPadTo length suffix str = str <> repeat (max 0 (length - strlen)) suffix
  where
  strlen = String.length str

repeat :: forall m. Monoid m => Int -> m -> m
repeat 0 str = mempty

repeat n str = str <> repeat (n - 1) str

unlines :: Array String -> String
unlines = String.joinWith "\n"

-- | Capitalize the first `Char` in a `String`
capitalize :: String -> String
capitalize str =
  let
    { before, after } = String.splitAt 1 str
  in
    String.toUpper before <> after

-- Absurdly, these two are not in the standard library
startsWith :: String.Pattern -> String -> Boolean
startsWith pattern = isJust <<< String.stripPrefix pattern

endsWith :: String.Pattern -> String -> Boolean
endsWith pattern = isJust <<< String.stripSuffix pattern
