module Data.Ratio_Type(module Data.Ratio_Type) where
import qualified Prelude()              -- do not import Prelude
import Primitives
import Data.Integer_Type

data Ratio a = !a :% !a

type Rational = Ratio Integer

_integerToRational :: Integer -> Rational
_integerToRational x = x :% (1::Integer)

_mkRational :: Integer -> Integer -> Rational
_mkRational = (:%)
