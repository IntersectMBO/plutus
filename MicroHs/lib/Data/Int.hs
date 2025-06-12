-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Int(Int, Int8, Int16, Int32, Int64) where
import qualified Prelude()              -- do not import Prelude
import Primitives
import Data.Bool_Type
import Data.Bounded
import Data.Char_Type
import Data.Eq
import Data.Int.IntN
import Data.Integer_Type
import Data.Integral
import Data.List_Type
import Data.Num
import Data.Ord
import Data.Ratio_Type
import Data.Real
import Text.Show

instance Num Int where
  (+)  = primIntAdd
  (-)  = primIntSub
  (*)  = primIntMul
  negate x = primIntNeg x
  abs x = if x < 0 then - x else x
  signum x =
    case compare x 0 of
      LT -> -1
      EQ ->  0
      GT ->  1
  fromInteger = _integerToInt

instance Integral Int where
  quot = primIntQuot
  rem  = primIntRem
  toInteger = _intToInteger

instance Bounded Int where
  minBound = primWordToInt ((primWordInv (0::Word) `primWordQuot` 2) `primWordAdd` 1)
  maxBound = primWordToInt  (primWordInv (0::Word) `primWordQuot` 2)

instance Real Int where
  toRational i = _integerToRational (_intToInteger i)

instance Eq Int where
  (==) = primIntEQ
  (/=) = primIntNE

instance Ord Int where
  compare = primIntCompare
  (<)  = primIntLT
  (<=) = primIntLE
  (>)  = primIntGT
  (>=) = primIntGE

instance Show Int where
  showsPrec p n r =
    if n < (0::Int) then
      if p > (6::Int) then
        '(' : '-' : showUnsignedNegInt n (')' : r)
      else
        '-' : showUnsignedNegInt n r
    else
      showUnsignedNegInt (- n) r

-- Some trickery to show minBound correctly.
-- To print the number n, pass -n.
showUnsignedNegInt :: Int -> ShowS
showUnsignedNegInt n r =
  let c = primChr (primOrd '0' - rem n (10::Int))
  in  if n > -(10::Int) then
        c : r
      else
        showUnsignedNegInt (quot n (10::Int)) (c : r)

--------------------------------

-- In Text.Read: instance Read Int
