module Data.Real(module Data.Real) where
import Data.Num
import Data.Ord
import Data.Ratio_Type
import Prelude qualified ()
import Primitives

class (Num a, Ord a) => Real a where
  toRational :: a -> Rational
