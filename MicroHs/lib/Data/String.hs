module Data.String(
  IsString(..),
  String,
  lines, unlines,
  words, unwords,
  ) where
import Data.Bool
import Data.Char
import Data.Eq
import Data.Function
import Data.List
import Prelude qualified ()

class IsString a where
  fromString :: String -> a

instance (a ~ Char) => IsString [a] where
  fromString s = s
