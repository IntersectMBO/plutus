{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -O2 -fno-warn-missing-signatures #-}
module Tests.Properties.Numeric where

import Data.Int (Int8, Int16, Int32, Int64)
import Data.Word (Word, Word8, Word16, Word32, Word64)
import Numeric (showEFloat, showFFloat, showGFloat, showHex)

import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck hiding ((.&.))
import Test.QuickCheck.Monadic

-- import GHC.Int
import Tests.QuickCheckUtils
import Tests.Utils

import qualified Data.JSString as J
import qualified Data.JSString.Int as JI
import qualified Data.JSString.RealFloat as JR

j_decimal :: (Integral a, Show a) => a -> Bool
j_decimal = show `eq` (J.unpack . JI.decimal)

j_decimal_integer (a::Integer) = j_decimal a
j_decimal_integer_big (Big a) = j_decimal a
j_decimal_int (a::Int) = j_decimal a
j_decimal_int8 (a::Int8) = j_decimal a
j_decimal_int16 (a::Int16) = j_decimal a
j_decimal_int32 (a::Int32) = j_decimal a
j_decimal_int64 (a::Int64) = j_decimal a
j_decimal_word (a::Word) = j_decimal a
j_decimal_word8 (a::Word8) = j_decimal a
j_decimal_word16 (a::Word16) = j_decimal a
j_decimal_word32 (a::Word32) = j_decimal a
j_decimal_word64 (a::Word64) = j_decimal a

j_decimal_int_big (BigBounded (a::Int)) = j_decimal a
j_decimal_int64_big (BigBounded (a::Int64)) = j_decimal a
j_decimal_word_big (BigBounded (a::Word)) = j_decimal a
j_decimal_word64_big (BigBounded (a::Word64)) = j_decimal a

j_hex :: (Integral a, Show a) => a -> Bool
j_hex = flip showHex "" `eq` (J.unpack . JI.hexadecimal)

j_hexadecimal_integer (a::Integer) = j_hex a
j_hexadecimal_int (a::Int) = j_hex a
j_hexadecimal_int8 (a::Int8) = j_hex a
j_hexadecimal_int16 (a::Int16) = j_hex a
j_hexadecimal_int32 (a::Int32) = j_hex a
j_hexadecimal_int64 (a::Int64) = j_hex a
j_hexadecimal_word (a::Word) = j_hex a
j_hexadecimal_word8 (a::Word8) = j_hex a
j_hexadecimal_word16 (a::Word16) = j_hex a
j_hexadecimal_word32 (a::Word32) = j_hex a
j_hexadecimal_word64 (a::Word64) = j_hex a

j_realfloat :: (RealFloat a, Show a) => a -> Bool
j_realfloat = (J.unpack . JR.realFloat) `eq` show

j_realfloat_float (a::Float) = j_realfloat a
j_realfloat_double (a::Double) = j_realfloat a


showFloat :: (RealFloat a) => JR.FPFormat -> Maybe Int -> a -> ShowS
showFloat JR.Exponent = showEFloat
showFloat JR.Fixed    = showFFloat
showFloat JR.Generic  = showGFloat

j_formatRealFloat :: (RealFloat a, Show a) =>
                      a -> JR.FPFormat -> Precision a -> Property
j_formatRealFloat a fmt prec =
    J.unpack (JR.formatRealFloat fmt p a) === showFloat fmt p a ""
  where p = precision a prec
{-# INLINE j_formatRealFloat #-}

j_formatRealFloat_float (a::Float) fmt prec   = -- j_formatRealFloat a
  J.unpack (JR.formatFloat fmt p a) === showFloat fmt p a ""
    where p = precision a prec
j_formatRealFloat_double (a::Double) fmt prec = --  j_formatRealFloat a
  J.unpack (JR.formatDouble fmt p a) === showFloat fmt p a ""
    where p = precision a prec
