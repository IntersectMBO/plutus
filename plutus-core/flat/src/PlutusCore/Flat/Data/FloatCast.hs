{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

{-| Primitives to convert between Float\/Double and Word32\/Word64.

Code copied from <https://hackage.haskell.org/package/binary binary>.

Based on: <http://hackage.haskell.org/package/reinterpret-cast-0.1.0/docs/src/Data-ReinterpretCast-Internal-ImplArray.html>..

Implements casting via a 1-element STUArray, as described in <http://stackoverflow.com/a/7002812/263061>. -}
module PlutusCore.Flat.Data.FloatCast
  ( floatToWord
  , wordToFloat
  , doubleToWord
  , wordToDouble
  , runST
  , cast
  )
where

import Data.Array.ST (MArray, STUArray, newArray, readArray)
import Data.Array.Unsafe (castSTUArray)
import Data.Word (Word32, Word64)
import GHC.ST (ST, runST)

-- import           Flat.Endian

{-| Reinterpret-casts a `Word32` to a `Float`.

prop> \f -> wordToFloat (floatToWord f ) == f
+++ OK, passed 100 tests.

>>> floatToWord (-0.15625)
3189768192

>>> wordToFloat 3189768192
-0.15625

>>> floatToWord (-5.828125) == 0xC0BA8000
True -}
wordToFloat :: Word32 -> Float
wordToFloat x = runST (cast x)
{-# INLINE wordToFloat #-}

-- | Reinterpret-casts a `Float` to a `Word32`.
floatToWord :: Float -> Word32
floatToWord x = runST (cast x)
{-# INLINE floatToWord #-}

{-$setup
>>> import Numeric (showHex)
>>> import Data.Word -}

{-|
Reinterpret-casts a `Double` to a `Word64`.

prop> \f -> wordToDouble (doubleToWord f ) == f
+++ OK, passed 100 tests.

>>> showHex (doubleToWord 1.0000000000000004) ""
"3ff0000000000002"

>>> doubleToWord 1.0000000000000004 == 0x3FF0000000000002
True

>>> showHex (doubleToWord (-0.15625)) ""
"bfc4000000000000"

>>> wordToDouble 0xbfc4000000000000
-0.15625 -}
{-# INLINE doubleToWord #-}
doubleToWord :: Double -> Word64
doubleToWord x = runST (cast x)

-- doubleToWord x = fix64 $ runST (cast x)

-- | Reinterpret-casts a `Word64` to a `Double`.
{-# INLINE wordToDouble #-}
wordToDouble :: Word64 -> Double
wordToDouble x = runST (cast x)

-- wordToDouble x = runST (cast $ fix64 x)

{-|
>>> runST (cast (0xF0F1F2F3F4F5F6F7::Word64)) == (0xF0F1F2F3F4F5F6F7::Word64)
True -}
cast
  :: (MArray (STUArray s) a (ST s), MArray (STUArray s) b (ST s)) => a -> ST s b
cast x = newArray (0 :: Int, 0) x >>= castSTUArray >>= flip readArray 0
{-# INLINE cast #-}
