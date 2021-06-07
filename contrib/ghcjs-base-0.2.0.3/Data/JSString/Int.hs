{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE JavaScriptFFI #-}
{-# LANGUAGE UnliftedFFITypes #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GHCForeignImportPrim #-}

module Data.JSString.Int
    ( decimal
    , hexadecimal
    ) where

import Data.JSString

import Data.Monoid

import GHC.Int
import GHC.Word
import GHC.Exts ( ByteArray#
                , Int(..), Int#, Int64#
                , Word(..), Word#, Word64#
                , (<#), (<=#), isTrue# )

import GHC.Integer.GMP.Internals
import Unsafe.Coerce
import GHCJS.Prim

decimal :: Integral a => a -> JSString
decimal i = decimal' i
{-# RULES "decimal/Int"     decimal = decimalI       :: Int     -> JSString #-}
{-# RULES "decimal/Int8"    decimal = decimalI8      :: Int8    -> JSString #-}
{-# RULES "decimal/Int16"   decimal = decimalI16     :: Int16   -> JSString #-}
{-# RULES "decimal/Int32"   decimal = decimalI32     :: Int32   -> JSString #-}
{-# RULES "decimal/Int64"   decimal = decimalI64     :: Int64   -> JSString #-}
{-# RULES "decimal/Word"    decimal = decimalW       :: Word    -> JSString #-}
{-# RULES "decimal/Word8"   decimal = decimalW8      :: Word8   -> JSString #-}
{-# RULES "decimal/Word16"  decimal = decimalW16     :: Word16  -> JSString #-}
{-# RULES "decimal/Word32"  decimal = decimalW32     :: Word32  -> JSString #-}
{-# RULES "decimal/Word64"  decimal = decimalW64     :: Word64  -> JSString #-}
{-# RULES "decimal/Integer" decimal = decimalInteger :: Integer -> JSString #-}
{-# SPECIALIZE decimal :: Integer -> JSString #-}
{-# SPECIALIZE decimal :: Int    -> JSString #-}
{-# SPECIALIZE decimal :: Int8   -> JSString #-}
{-# SPECIALIZE decimal :: Int16  -> JSString #-}
{-# SPECIALIZE decimal :: Int32  -> JSString #-}
{-# SPECIALIZE decimal :: Int64  -> JSString #-}
{-# SPECIALIZE decimal :: Word   -> JSString #-}
{-# SPECIALIZE decimal :: Word8  -> JSString #-}
{-# SPECIALIZE decimal :: Word16 -> JSString #-}
{-# SPECIALIZE decimal :: Word32 -> JSString #-}
{-# SPECIALIZE decimal :: Word64 -> JSString #-}
{-# INLINE [1] decimal #-}

decimalI :: Int -> JSString
decimalI (I# x) = js_decI x
{-# INLINE decimalI #-}

decimalI8 :: Int8 -> JSString
decimalI8 (I8# x) = js_decI x
{-# INLINE decimalI8 #-}

decimalI16 :: Int16 -> JSString
decimalI16 (I16# x) = js_decI x
{-# INLINE decimalI16 #-}

decimalI32 :: Int32 -> JSString
decimalI32 (I32# x) = js_decI x
{-# INLINE decimalI32 #-}

decimalI64 :: Int64 -> JSString
decimalI64 (I64# x) = js_decI64 x
{-# INLINE decimalI64 #-}

decimalW8 :: Word8 -> JSString
decimalW8 (W8# x) = js_decW x
{-# INLINE decimalW8 #-}

decimalW16 :: Word16 -> JSString
decimalW16 (W16# x) = js_decW x
{-# INLINE decimalW16 #-}

decimalW32 :: Word32 -> JSString
decimalW32 (W32# x) = js_decW32 x
{-# INLINE decimalW32 #-}

decimalW64 :: Word64 -> JSString
decimalW64 (W64# x) = js_decW64 x
{-# INLINE decimalW64 #-}

decimalW :: Word -> JSString
decimalW (W# x) = js_decW32 x
{-# INLINE decimalW #-}

-- hack warning, we should really expose J# somehow
data MyI = MyS Int# | MyJ Int# ByteArray#

decimalInteger :: Integer -> JSString
decimalInteger !i = js_decInteger (unsafeCoerce i)
{-# INLINE decimalInteger #-}

decimal' :: Integral a => a -> JSString
decimal' i = decimalInteger (toInteger i)
{-# NOINLINE decimal' #-}
{-
  | i < 0 = if i <= -10
              then let (q, r)   = i `quotRem` (-10)
                       !(I# rr) = fromIntegral r
                   in  js_minusDigit (positive q) rr
              else js_minus (positive (negate i))
  | otherwise = positive i

positive :: (Integral a) => a -> JSString
positive i
  | toInteger i < 1000000000 = let !(I# x) = fromIntegral i in js_decI x
  | otherwise                = let (q, r)  = i `quotRem` 1000000000
                                   !(I# x) = fromIntegral r
                               in  positive q <> js_decIPadded9 x
-}

hexadecimal :: Integral a => a -> JSString
hexadecimal i = hexadecimal' i
{-# RULES "hexadecimal/Int"     hexadecimal = hexI       :: Int     -> JSString #-}
{-# RULES "hexadecimal/Int8"    hexadecimal = hexI8      :: Int8    -> JSString #-}
{-# RULES "hexadecimal/Int16"   hexadecimal = hexI16     :: Int16   -> JSString #-}
{-# RULES "hexadecimal/Int32"   hexadecimal = hexI32     :: Int32   -> JSString #-}
{-# RULES "hexadecimal/Int64"   hexadecimal = hexI64     :: Int64   -> JSString #-}
{-# RULES "hexadecimal/Word"    hexadecimal = hexW       :: Word    -> JSString #-}
{-# RULES "hexadecimal/Word8"   hexadecimal = hexW8      :: Word8   -> JSString #-}
{-# RULES "hexadecimal/Word16"  hexadecimal = hexW16     :: Word16  -> JSString #-}
{-# RULES "hexadecimal/Word32"  hexadecimal = hexW32     :: Word32  -> JSString #-}
{-# RULES "hexadecimal/Word64"  hexadecimal = hexW64     :: Word64  -> JSString #-}
{-# RULES "hexadecimal/Integer" hexadecimal = hexInteger :: Integer -> JSString #-}
{-# SPECIALIZE hexadecimal :: Integer -> JSString #-}
{-# SPECIALIZE hexadecimal :: Int    -> JSString #-}
{-# SPECIALIZE hexadecimal :: Int8   -> JSString #-}
{-# SPECIALIZE hexadecimal :: Int16  -> JSString #-}
{-# SPECIALIZE hexadecimal :: Int32  -> JSString #-}
{-# SPECIALIZE hexadecimal :: Int64  -> JSString #-}
{-# SPECIALIZE hexadecimal :: Word   -> JSString #-}
{-# SPECIALIZE hexadecimal :: Word8  -> JSString #-}
{-# SPECIALIZE hexadecimal :: Word16 -> JSString #-}
{-# SPECIALIZE hexadecimal :: Word32 -> JSString #-}
{-# SPECIALIZE hexadecimal :: Word64 -> JSString #-}
{-# INLINE [1] hexadecimal #-}

hexadecimal' :: Integral a => a -> JSString
hexadecimal' i
    | i < 0     = error hexErrMsg
    | otherwise = hexInteger (toInteger i)
{-# NOINLINE hexadecimal' #-}

hexInteger :: Integer -> JSString
hexInteger !i
  | i < 0     = error hexErrMsg
  | otherwise = js_hexInteger (unsafeCoerce i)
{-# INLINE hexInteger #-}

hexI :: Int -> JSString
hexI (I# x) = if isTrue# (x <# 0#)
              then error hexErrMsg
              else js_hexI x
{-# INLINE hexI #-}

hexI8 :: Int8 -> JSString
hexI8 (I8# x) =
  if isTrue# (x <# 0#)
  then error hexErrMsg
  else js_hexI x
{-# INLINE hexI8 #-}

hexI16 :: Int16 -> JSString
hexI16 (I16# x) =
  if isTrue# (x <# 0#)
  then error hexErrMsg
  else js_hexI x
{-# INLINE hexI16 #-}

hexI32 :: Int32 -> JSString
hexI32 (I32# x) =
  if isTrue# (x <# 0#)
  then error hexErrMsg
  else js_hexI x
{-# INLINE hexI32 #-}

hexI64 :: Int64 -> JSString
hexI64 i@(I64# x) =
  if i < 0
  then error hexErrMsg
  else js_hexI64 x
{-# INLINE hexI64 #-}

hexW :: Word -> JSString
hexW (W# x) = js_hexW32 x
{-# INLINE hexW #-}

hexW8 :: Word8 -> JSString
hexW8 (W8# x) = js_hexW x
{-# INLINE hexW8 #-}

hexW16 :: Word16 -> JSString
hexW16 (W16# x) = js_hexW x
{-# INLINE hexW16 #-}

hexW32 :: Word32 -> JSString
hexW32 (W32# x) = js_hexW32 x
{-# INLINE hexW32 #-}

hexW64 :: Word64 -> JSString
hexW64 (W64# x) = js_hexW64 x
{-# INLINE hexW64 #-}

hexErrMsg :: String
hexErrMsg = "Data.JSString.Int.hexadecimal: applied to negative number"

-- ----------------------------------------------------------------------------

foreign import javascript unsafe
  "''+$1"
  js_decI       :: Int#     -> JSString
foreign import javascript unsafe
  "h$jsstringDecI64"
  js_decI64     :: Int64#   -> JSString
foreign import javascript unsafe
  "''+$1"
  js_decW       :: Word#    -> JSString
foreign import javascript unsafe
  "''+(($1>=0)?$1:($1+4294967296))"
  js_decW32     :: Word#    -> JSString
foreign import javascript unsafe
  "h$jsstringDecW64($1_1, $1_2)"
  js_decW64     :: Word64#  -> JSString
foreign import javascript unsafe
  "h$jsstringDecInteger($1)"
  js_decInteger :: Any -> JSString

-- these are expected to be only applied to nonnegative integers
foreign import javascript unsafe
  "$1.toString(16)"
  js_hexI       :: Int#    -> JSString
foreign import javascript unsafe
  "h$jsstringHexI64"
  js_hexI64     :: Int64#   -> JSString

foreign import javascript unsafe
  "$1.toString(16)"
  js_hexW       :: Word#    -> JSString
foreign import javascript unsafe
  "(($1>=0)?$1:($1+4294967296)).toString(16)"
  js_hexW32     :: Word#    -> JSString
foreign import javascript unsafe
  "h$jsstringHexW64($1_1, $1_2)"
  js_hexW64     :: Word64#  -> JSString
foreign import javascript unsafe
  "h$jsstringHexInteger($1)"
  js_hexInteger :: Any -> JSString

foreign import javascript unsafe
  "'-'+$1+(-$2)"
  js_minusDigit :: JSString -> Int# -> JSString
foreign import javascript unsafe
  "'-'+$1"
  js_minus :: JSString -> JSString

--
foreign import javascript unsafe
  "h$jsstringDecIPadded9"
  js_decIPadded9 :: Int# -> JSString
foreign import javascript unsafe
  "h$jsstringHexIPadded8"
  js_hexIPadded8 :: Int# -> JSString
