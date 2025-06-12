module Data.Enum (
  Enum(..),
  boundedEnumFrom,
  boundedEnumFromThen,
  numericEnumFrom,
  numericEnumFromThen,
  numericEnumFromTo,
  numericEnumFromThenTo,
) where
import Control.Error
import Data.Bool
import Data.Bounded
import Data.Char_Type
import Data.Enum_Class
import Data.Function
import Data.Int
import Data.List
import Data.Num
import Data.Ord
import Prelude qualified ()
import Primitives

boundedEnumFrom :: forall a . (Enum a, Bounded a) => a -> [a]
boundedEnumFrom n = map toEnum [fromEnum n .. fromEnum (maxBound `asTypeOf` n)]

boundedEnumFromThen :: forall a . (Enum a, Bounded a) => a -> a -> [a]
boundedEnumFromThen n1 n2
  | i_n2 >= i_n1  = map toEnum [i_n1, i_n2 .. fromEnum (maxBound `asTypeOf` n1)]
  | otherwise     = map toEnum [i_n1, i_n2 .. fromEnum (minBound `asTypeOf` n1)]
  where
    i_n1 = fromEnum n1
    i_n2 = fromEnum n2

numericEnumFrom :: (Num a) => a -> [a]
numericEnumFrom n = n : numericEnumFrom (n + 1)

numericEnumFromThen :: (Num a) => a -> a -> [a]
numericEnumFromThen n m = from n
  where
    d = m - n
    from i = i : from (i + d)

numericEnumFromTo :: (Num a, Ord a) => a -> a -> [a]
numericEnumFromTo l h = takeWhile (<= h) (numericEnumFrom l)

numericEnumFromThenTo :: (Num a, Ord a) => a -> a -> a -> [a]
numericEnumFromThenTo l m h =
  if m > l then
    takeWhile (<= h) (numericEnumFromThen l m)
  else
    takeWhile (>= h) (numericEnumFromThen l m)

-- Likewise for Bool
instance Enum Bool where
  fromEnum False = 0
  fromEnum True  = 1
  toEnum i
    | i `primIntEQ` 0 = False
    | i `primIntEQ` 1 = True
    | otherwise       = error "Enum.Bool.toEnum: bad arg"
  enumFrom = boundedEnumFrom
  enumFromThen = boundedEnumFromThen

instance Enum Char where
  fromEnum = primOrd
  toEnum   = primChr
  enumFrom = boundedEnumFrom
  enumFromThen = boundedEnumFromThen

instance Enum Ordering where
  fromEnum LT = 0
  fromEnum EQ = 1
  fromEnum GT = 2
  toEnum i
    | i `primIntEQ` 0 = LT
    | i `primIntEQ` 1 = EQ
    | i `primIntEQ` 2 = GT
    | otherwise       = error "Ord.toEnum: out of range"
  enumFrom = boundedEnumFrom
  enumFromThen = boundedEnumFromThen
