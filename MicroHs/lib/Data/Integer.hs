-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Integer(
  Integer,
  _integerToIntList,
  _intListToInteger,
  ) where
import qualified Prelude()              -- do not import Prelude
import Data.Bits
import Data.Bool
import Data.Enum
import Data.Eq
import Data.Int
import Data.Integer.Internal
import Data.Integral
import Data.List
import Data.Maybe_Type
import Data.Num
import Data.Ord
import Data.Ratio_Type
import Data.Real
import Numeric.Show
import Text.Show

-- This module does not know about the representation of Integer.
-- It uses functions defined in Data.Integer.Internal

instance Eq Integer where
  (==) = eqI
  (/=) = neI

instance Ord Integer where
  compare = cmpI
  (<)  = ltI
  (<=) = leI
  (>)  = gtI
  (>=) = geI

instance Show Integer where
  showsPrec = showIntegral

{- in Text.Read.Internal
instance Read Integer
-}

instance Num Integer where
  (+) = addI
  (-) = subI
  (*) = mulI
  negate = negateI
  abs = absI
  signum x =
    case compare x zeroI of
      LT -> negOneI
      EQ -> zeroI
      GT -> oneI
  fromInteger x = x

instance Integral Integer where
  quotRem = quotRemI
  toInteger x = x

instance Real Integer where
  toRational i = _integerToRational i

instance Enum Integer where
  succ x = x + 1
  pred x = x - 1
  toEnum x = _intToInteger x
  fromEnum x = _integerToInt x
  enumFrom = numericEnumFrom
  enumFromThen = numericEnumFromThen
  enumFromTo = numericEnumFromTo
  enumFromThenTo = numericEnumFromThenTo

instance Bits Integer where
  (.&.) = andI
  (.|.) = orI
  xor = xorI
  complement x = negOneI - x -- -x = complement x + 1 => complement x = -1 - x
  unsafeShiftL = shiftLI
  x `shiftL` i
    | i < 0 = _overflowError
    | otherwise = x `unsafeShiftL` i
  unsafeShiftR = shiftRI
  x `shiftR` i
    | i < 0 = _overflowError
    | otherwise = x `unsafeShiftR` i
  x `shift` i
    | i < 0 = x `unsafeShiftR` (-i)
    | i > 0 = x `unsafeShiftL` i
    | otherwise = x
  rotate = shift
  bit i = oneI `shiftL` i
  testBit = testBitI
  zeroBits = zeroI
  bitSizeMaybe _ = Nothing
  popCount = popCountI
  isSigned _ = True

-----------------

-- For the combinator file we need a portable way to store
-- the Integer type.  We use [Int], with digits in a small base.
integerListBase :: Integer
integerListBase = _intToInteger 32768

-- These two functions return an (opaque) representation of an
-- Integer as [Int].
-- This is used by the compiler to generate Integer literals.
-- First _integerToIntList is used in the compiler to get a list of
-- Int, and the generated code will have a call to _intListToInteger.
_integerToIntList :: Integer -> [Int]
_integerToIntList i = if i < 0 then (-1::Int) : f (-i) else f i
  where f 0 = []
        f i = fromInteger r : f q  where (q, r) = quotRem i integerListBase

_intListToInteger :: [Int] -> Integer
_intListToInteger [] = _intToInteger 0
_intListToInteger ads@(x : ds) = if x == -1 then - f ds else f ads
  where f = foldr (\ d a -> a * integerListBase + toInteger d) 0

