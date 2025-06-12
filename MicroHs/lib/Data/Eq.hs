module Data.Eq(
  module Data.Eq
  ) where
import qualified Prelude()              -- do not import Prelude
import Primitives
import Data.Bool_Type

infix 4 ==,/=

class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool
  x /= y = if x == y then False else True
