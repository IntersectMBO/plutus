{-# LANGUAGE ForeignFunctionInterface, JavaScriptFFI, UnliftedFFITypes,
             GHCForeignImportPrim, UnboxedTuples, BangPatterns,
             MagicHash
  #-}
module Data.JSString.Read ( isInteger
                          , isNatural
                          , readInt
                          , readIntMaybe
                          , lenientReadInt
                          , readInt64
                          , readInt64Maybe
                          , readWord64
                          , readWord64Maybe
                          , readDouble
                          , readDoubleMaybe
                          , readInteger
                          , readIntegerMaybe
                          ) where

import GHCJS.Types

import GHC.Exts (Any, Int#, Int64#, Word64#, Int(..))
import GHC.Int (Int64(..))
import GHC.Word (Word64(..))
import Unsafe.Coerce
import Data.Maybe
import Data.JSString

{- |
    Returns whether the JSString represents an integer at base 10
 -}
isInteger :: JSString -> Bool
isInteger j = js_isInteger j
{-# INLINE isInteger #-}

{- |
    Returns whether the JSString represents a natural number at base 10
    (including 0)
 -}
isNatural :: JSString -> Bool
isNatural j = js_isInteger j
{-# INLINE isNatural #-}

{- |
     Convert a JSString to an Int, throwing an exception if it cannot
     be converted. Leading spaces are allowed. The function ignores
     trailing non-digit characters.
 -}
lenientReadInt :: JSString -> Int
lenientReadInt j = fromMaybe (readError "lenientReadInt") (lenientReadIntMaybe j)
{-# INLINE lenientReadInt #-}

{- |
     Convert a JSString to an Int, returning Nothing if it cannot
     be converted. Leading spaces are allowed. The function ignores
     trailing non-digit characters.
 -}
lenientReadIntMaybe :: JSString -> Maybe Int
lenientReadIntMaybe j = convertNullMaybe js_lenientReadInt j
{-# INLINE lenientReadIntMaybe #-}

{- |
     Convert a JSString to an Int, throwing an exception if it cannot
     be converted. Leading spaces and trailing non-digit characters
     are not allowed.
 -}
readInt :: JSString -> Int
readInt j = fromMaybe (readError "readInt") (readIntMaybe j)
{-# INLINE readInt #-}

{- |
     Convert a JSString to an Int, returning Nothing if it cannot
     be converted. Leading spaces and trailing non-digit characters
     are not allowed.
 -}
readIntMaybe :: JSString -> Maybe Int
readIntMaybe j = convertNullMaybe js_readInt j
{-# INLINE readIntMaybe #-}

readInt64 :: JSString -> Int64
readInt64 j = fromMaybe (readError "readInt64") (readInt64Maybe j)
{-# INLINE readInt64 #-}

readInt64Maybe :: JSString -> Maybe Int64
readInt64Maybe j = case js_readInt64 j of
                     (# 0#, _ #) -> Nothing
                     (#  _, x #) -> Just (I64# x)
{-# INLINE readInt64Maybe #-}

readWord64 :: JSString -> Word64
readWord64 j = fromMaybe (readError "readWord64") (readWord64Maybe j)
{-# INLINE readWord64 #-}

readWord64Maybe :: JSString -> Maybe Word64
readWord64Maybe j = case js_readWord64 j of
                     (# 0#, _ #) -> Nothing
                     (#  _, x #) -> Just (W64# x)
{-# INLINE readWord64Maybe #-}


{- |
     Convert a JSString to an Int, throwing an exception if it cannot
     be converted. Leading spaces are allowed. The function ignores
     trailing non-digit characters.
 -}
readDouble :: JSString -> Double
readDouble j = fromMaybe (readError "readDouble") (readDoubleMaybe j)
{-# INLINE readDouble #-}

{- |
     Convert a JSString to a Double, returning Nothing if it cannot
     be converted. Leading spaces are allowed. The function ignores
     trailing non-digit characters.
 -}

readDoubleMaybe :: JSString -> Maybe Double
readDoubleMaybe j = convertNullMaybe js_readDouble j
{-# INLINE readDoubleMaybe #-}

{- |
     Convert a JSString to a Double, returning Nothing if it cannot
     be converted. Leading spaces and trailing non-digit characters
     are not allowed.
 -}
strictReadDoubleMaybe :: JSString -> Maybe Double
strictReadDoubleMaybe j = convertNullMaybe js_readDouble j
{-# INLINE strictReadDoubleMaybe #-}

readInteger :: JSString -> Integer
readInteger j = fromMaybe (readError "readInteger") (readIntegerMaybe j)
{-# INLINE readInteger #-}

readIntegerMaybe :: JSString -> Maybe Integer
readIntegerMaybe j = convertNullMaybe js_readInteger j
{-# INLINE readIntegerMaybe #-}

-- ----------------------------------------------------------------------------

convertNullMaybe :: (JSString -> JSVal) -> JSString -> Maybe a
convertNullMaybe f j
  | js_isNull r = Nothing
  | otherwise   = Just (unsafeCoerce (js_toHeapObject r))
  where
    r = f j
{-# INLINE convertNullMaybe #-}

readError :: String -> a
readError xs = error ("Data.JSString.Read." ++ xs)

-- ----------------------------------------------------------------------------

foreign import javascript unsafe
  "$r = $1===null;" js_isNull :: JSVal -> Bool
foreign import javascript unsafe
  "$r=$1;" js_toHeapObject :: JSVal -> Any
foreign import javascript unsafe
  "h$jsstringReadInteger" js_readInteger :: JSString -> JSVal
foreign import javascript unsafe
  "h$jsstringReadInt" js_readInt :: JSString -> JSVal
foreign import javascript unsafe
  "h$jsstringLenientReadInt" js_lenientReadInt :: JSString -> JSVal
foreign import javascript unsafe
  "h$jsstringReadInt64" js_readInt64 :: JSString -> (# Int#, Int64# #)
foreign import javascript unsafe
  "h$jsstringReadWord64" js_readWord64 :: JSString -> (# Int#, Word64# #)
foreign import javascript unsafe
  "h$jsstringReadDouble" js_readDouble :: JSString -> JSVal
foreign import javascript unsafe
  "h$jsstringIsInteger" js_isInteger :: JSString -> Bool
foreign import javascript unsafe
  "h$jsstringIsNatural" js_isNatural :: JSString -> Bool
