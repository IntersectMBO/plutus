-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.FloatW(FloatW) where
import qualified Prelude()              -- do not import Prelude
import Primitives
import Control.Error
import Data.Bits
import Data.Bool
import Data.Char
import Data.Enum
import Data.Eq
import Data.Floating
import Data.Fractional
import Data.Function
import Data.Integer
import Data.Integer.Internal(_integerToFloatW, _wordToInteger)
import Data.Integral
import Data.List
import Data.Ord
import Data.Ratio
import Data.Real
import Data.RealFloat
import Data.RealFrac
import Data.Num
import Data.Word
import Text.Show

--
-- This is a floating point type that is a wide as the word width of the machine.
--

instance Num FloatW where
  (+)  = primFloatWAdd
  (-)  = primFloatWSub
  (*)  = primFloatWMul
  negate = primFloatWNeg
  abs x = if x < 0.0 then - x else x
  signum x =
    case compare x 0.0 of
      LT -> -1.0
      EQ ->  0.0
      GT ->  1.0
  fromInteger = _integerToFloatW

instance Fractional FloatW where
  (/) = primFloatWDiv
  -- This version of fromRational can go horribly wrong
  -- if the integers are bigger than can be represented in a FloatW.
  -- It'll do for now.
  fromRational x | x == rationalNaN = 0/0
                 | x == rationalInfinity = 1/0
                 | x == -rationalInfinity = (-1)/0
                 | otherwise =
    fromInteger (numerator x) / fromInteger (denominator x)

instance Eq FloatW where
  (==) = primFloatWEQ
  (/=) = primFloatWNE

instance Ord FloatW where
  (<)  = primFloatWLT
  (<=) = primFloatWLE
  (>)  = primFloatWGT
  (>=) = primFloatWGE

-- For now, cheat and call C
instance Show FloatW where
  show = primFloatWShow -- should be Numeric.FormatFloat.showFloat, but that drags in a lot of stuff

{- in Text.Read.Internal
instance Read FloatW where
  readsPrec _ = readSigned $ \ r -> [ (primFloatWRead s, t) | (s@(c:_), t) <- lex r, isDigit c ]
-}

instance Enum FloatW where
  succ x = x + 1
  pred x = x - 1
  toEnum n = fromIntegral n
  fromEnum = fromInteger . truncate
  enumFrom = numericEnumFrom
  enumFromThen = numericEnumFromThen
  enumFromTo = numericEnumFromTo
  enumFromThenTo = numericEnumFromThenTo

instance Real FloatW where
  toRational x | isNaN x = rationalNaN
               | isInfinite x = if x < 0 then -rationalInfinity else rationalInfinity
               | otherwise =
    case decodeFloat x of
      (m, e) -> toRational m * 2^^e

instance RealFrac FloatW where
  properFraction x =
    case decodeFloat x of
      (m, e) ->   -- x = m * 2^e
        let m' | e < 0     = m `quot` 2^(-e)
               | otherwise = m * 2^e
        in  (fromInteger m', x - fromInteger m')

instance Floating FloatW where
  pi     = 3.141592653589793
  log  x = primPerformIO (clog x)
  exp  x = primPerformIO (cexp x)
  sqrt x = primPerformIO (csqrt x)
  sin  x = primPerformIO (csin x)
  cos  x = primPerformIO (ccos x)
  tan  x = primPerformIO (ctan x)
  asin x = primPerformIO (casin x)
  acos x = primPerformIO (cacos x)
  atan x = primPerformIO (catan x)

foreign import ccall "log"  clog  :: FloatW -> IO FloatW
foreign import ccall "exp"  cexp  :: FloatW -> IO FloatW
foreign import ccall "sqrt" csqrt :: FloatW -> IO FloatW
foreign import ccall "sin"  csin  :: FloatW -> IO FloatW
foreign import ccall "cos"  ccos  :: FloatW -> IO FloatW
foreign import ccall "tan"  ctan  :: FloatW -> IO FloatW
foreign import ccall "asin" casin :: FloatW -> IO FloatW
foreign import ccall "acos" cacos :: FloatW -> IO FloatW
foreign import ccall "atan" catan :: FloatW -> IO FloatW
foreign import ccall "atan2" catan2 :: FloatW -> FloatW -> IO FloatW

-- Assumes 32/64 bit floats
instance RealFloat FloatW where
  floatRadix     _ = 2
  floatDigits    _ = flt 24 53
  floatRange     _ = flt (-125,128) (-1021,1024)
  decodeFloat      = flt decodeFloat32 decodeFloat64
  encodeFloat      = flt encodeFloat32 encodeFloat64
  isNaN            = flt isNaNFloat32 isNaNFloat64
  isInfinite       = flt isInfFloat32 isInfFloat64
  isDenormalized   = flt isDenFloat32 isDenFloat64
  isNegativeZero   = flt isNegZeroFloat32 isNegZeroFloat64
  isIEEE         _ = True
  atan2 x y        = primPerformIO (catan2 x y)

flt :: forall a . a -> a -> a
flt f d | _wordSize == 32 = f
        | otherwise       = d

decodeFloat64 :: FloatW -> (Integer, Int)
decodeFloat64 x =
  let xw   = primWordFromFloatWRaw x
      sign =  xw .&. 0x8000000000000000
      expn = (xw .&. 0x7fffffffffffffff) `shiftR` 52
      mant =  xw .&. 0x000fffffffffffff
      neg  = if sign /= 0 then negate else id
  in  if expn == 0 then
        -- subnormal or 0
        (neg (_wordToInteger mant), 0)
      else if expn == 0x7ff then
        -- infinity or NaN
        (0, 0)
      else
        -- ordinary number, add hidden bit
        -- mant is offset-1023, and assumes scaled mantissa (thus -52)
        (neg (_wordToInteger (mant .|. 0x0010000000000000)),
         primWordToInt expn - 1023 - 52)

isNaNFloat64 :: FloatW -> Bool
isNaNFloat64 x =
  let xw   = primWordFromFloatWRaw x
      expn = (xw .&. 0x7fffffffffffffff) `shiftR` 52
      mant =  xw .&. 0x000fffffffffffff
  in  expn == 0x7ff && mant /= 0

isInfFloat64 :: FloatW -> Bool
isInfFloat64 x =
  let xw   = primWordFromFloatWRaw x
      expn = (xw .&. 0x7fffffffffffffff) `shiftR` 52
      mant =  xw .&. 0x000fffffffffffff
  in  expn == 0x7ff && mant == 0

isDenFloat64 :: FloatW -> Bool
isDenFloat64 x =
  let xw   = primWordFromFloatWRaw x
      expn = (xw .&. 0x7fffffffffffffff) `shiftR` 52
      mant =  xw .&. 0x000fffffffffffff
  in  expn == 0 && mant /= 0

isNegZeroFloat64 :: FloatW -> Bool
isNegZeroFloat64 x =
  let xw   = primWordFromFloatWRaw x
      sign = xw .&. 0x8000000000000000
      rest = xw .&. 0x7fffffffffffffff
  in  sign /= 0 && rest == 0

-- Simple (and sometimes wrong) encoder
encodeFloat64 :: Integer -> Int -> FloatW
encodeFloat64 mant expn = fromInteger mant * 2^^expn

decodeFloat32 :: FloatW -> (Integer, Int)
decodeFloat32 x =
  let xw   = primWordFromFloatWRaw x
      sign =  xw .&. 0x80000000
      expn = (xw .&. 0x7fffffff) `shiftR` 23
      mant =  xw .&. 0x007fffff
      neg  = if sign /= 0 then negate else id
  in  if expn == 0 then
        -- subnormal or 0
        (neg (_wordToInteger mant), 0)
      else if expn == 0xff then
        -- infinity or NaN
        (0, 0)
      else
        -- ordinary number, add hidden bit
        -- mant is offset-1023, and assumes scaled mantissa (thus -52)
        (neg (_wordToInteger (mant .|. 0x00400000)),
         primWordToInt expn - 127 - 22)

isNaNFloat32 :: FloatW -> Bool
isNaNFloat32 x =
  let xw   = primWordFromFloatWRaw x
      expn = (xw .&. 0x7fffffff) `shiftR` 23
      mant =  xw .&. 0x007fffff
  in  expn == 0xff && mant /= 0

isInfFloat32 :: FloatW -> Bool
isInfFloat32 x =
  let xw   = primWordFromFloatWRaw x
      expn = (xw .&. 0x7fffffff) `shiftR` 23
      mant =  xw .&. 0x007fffff
  in  expn == 0x7ff && mant == 0

isDenFloat32 :: FloatW -> Bool
isDenFloat32 x =
  let xw   = primWordFromFloatWRaw x
      expn = (xw .&. 0x7fffffff) `shiftR` 23
      mant =  xw .&. 0x007fffff
  in  expn == 0 && mant /= 0

isNegZeroFloat32 :: FloatW -> Bool
isNegZeroFloat32 x =
  let xw   = primWordFromFloatWRaw x
      sign = xw .&. 0x80000000
      rest = xw .&. 0x7fffffff
  in  sign /= 0 && rest == 0

-- Simple (and sometimes wrong) encoder
encodeFloat32 :: Integer -> Int -> FloatW
encodeFloat32 mant expn = fromInteger mant * 2^^expn
