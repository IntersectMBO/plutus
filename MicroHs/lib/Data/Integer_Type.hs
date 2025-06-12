-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Integer_Type(module Data.Integer_Type) where
import {-# SOURCE #-} Control.Error
import Data.Bool_Type
import Data.List_Type
import Prelude qualified ()
import Primitives

--
-- The Integer is stored in sign-magnitude format with digits in base maxD (2^32)
-- It has the following invariants:
--  * each digit is >= 0 and < maxD
--  * least significant digits first, most significant last
--  * no trailing 0s in the digits
--  * 0 is positive

data Integer = I Sign [Digit]

data Sign = Plus | Minus

type Digit = Word

maxD :: Digit
maxD = 1 `primWordShl` shiftD

shiftD :: Int
shiftD = _wordSize `primIntShr` 1 -- this is used so multiplication of two digits doesn't overflow a Word

quotMaxD :: Digit -> Digit
quotMaxD d = d `primWordShr` shiftD

remMaxD :: Digit -> Digit
remMaxD d = d `primWordAnd` (maxD `primWordSub` 1)

-- Sadly, we also need a bunch of functions.

_intToInteger :: Int -> Integer
_intToInteger i
  | i `primIntEQ` 0 = I Plus []
  | i `primIntGE` 0 = f Plus (primIntToWord i)
  | True            = f Minus (primIntToWord (0 `primIntSub` i))
  where
    f sign i =
      let
        high = quotMaxD i
        low = remMaxD i
      in if high `primWordEQ` 0 then I sign [low] else I sign [low, high]

_integerToInt :: Integer -> Int
_integerToInt x = primWordToInt (_integerToWord x)

_wordToInteger :: Word -> Integer
_wordToInteger i
  | i    `primWordEQ` 0 = I Plus []
  | high `primWordEQ` 0 = I Plus [low]
  | True                = I Plus [low, high]
  where
    high = quotMaxD i
    low = remMaxD i

_integerToWord :: Integer -> Word
_integerToWord (I sign ds) =
  case sign of
    Plus  -> i
    Minus -> 0 `primWordSub` i
  where
    i =
      case ds of
        []          -> 0 :: Word
        [d1]        -> d1
        d1 : d2 : _ -> d1 `primWordAdd` (d2 `primWordShl` shiftD)

_integerToFloatW :: Integer -> FloatW
_integerToFloatW (I sign ds) = s `primFloatWMul` loop ds
  where
    loop [] = 0.0 :: FloatW
    loop (d : ds) = primFloatWFromInt (primWordToInt d) `primFloatWAdd` (primFloatWFromInt (primWordToInt maxD) `primFloatWMul` loop ds)
    s =
      case sign of
        Plus  -> 1.0 :: FloatW
        Minus -> 0.0 `primFloatWSub` 1.0
