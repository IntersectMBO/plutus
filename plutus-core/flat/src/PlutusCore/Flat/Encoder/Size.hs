{-# LANGUAGE CPP #-}

-- |Primitives to calculate the maximum size in bits of the encoding of a value
module PlutusCore.Flat.Encoder.Size where

import Data.Bits (Bits)
import Data.ByteString qualified as B
import Data.ByteString.Lazy qualified as L
import Data.ByteString.Short.Internal qualified as SBS
import Data.Char (ord)
import Data.Text qualified as T
import Data.Text.Internal qualified as TI
import PlutusCore.Flat.Data.ZigZag (ZigZag (zigZag))
import PlutusCore.Flat.Encoder.Prim (w7l)
import PlutusCore.Flat.Types (Int16, Int32, Int64, Natural, NumBits, Text, Word16, Word32, Word64)
#include "MachDeps.h"
-- A filler can take anything from 1 to 8 bits
sFillerMax :: NumBits
sFillerMax = 8

sBool :: NumBits
sBool = 1

sWord8 :: NumBits
sWord8 = 8

sInt8 :: NumBits
sInt8 = 8

sFloat :: NumBits
sFloat = 32

sDouble :: NumBits
sDouble = 64

{-# INLINE sChar #-}
sChar :: Char -> NumBits
sChar = sWord32 . fromIntegral . ord

sCharMax :: NumBits
sCharMax = 24

{-# INLINE sWord #-}
sWord :: Word -> NumBits
{-# INLINE sInt #-}
sInt :: Int -> NumBits
#if WORD_SIZE_IN_BITS == 64
sWord = sWord64 . fromIntegral

sInt = sInt64 . fromIntegral
#elif WORD_SIZE_IN_BITS == 32
sWord = sWord32 . fromIntegral

sInt = sInt32 . fromIntegral
#else
#error expected WORD_SIZE_IN_BITS to be 32 or 64
#endif
-- TODO: optimize ints sizes
{-# INLINE sInt16 #-}
sInt16 :: Int16 -> NumBits
sInt16 = sWord16 . zigZag

{-# INLINE sInt32 #-}
sInt32 :: Int32 -> NumBits
sInt32 = sWord32 . zigZag

{-# INLINE sInt64 #-}
sInt64 :: Int64 -> NumBits
sInt64 = sWord64 . zigZag

{-# INLINE sWord16 #-}
sWord16 :: Word16 -> NumBits
sWord16 w
  | w < 128 = 8
  | w < 16384 = 16
  | otherwise = 24

{-# INLINE sWord32 #-}
sWord32 :: Word32 -> NumBits
sWord32 w
  | w < 128 = 8
  | w < 16384 = 16
  | w < 2097152 = 24
  | w < 268435456 = 32
  | otherwise = 40

{-# INLINE sWord64 #-}
sWord64 :: Word64 -> NumBits
sWord64 w
  | w < 128 = 8
  | w < 16384 = 16
  | w < 2097152 = 24
  | w < 268435456 = 32
  | w < 34359738368 = 40
  | w < 4398046511104 = 48
  | w < 562949953421312 = 56
  | w < 72057594037927936 = 64
  | w < 9223372036854775808 = 72
  | otherwise = 80

{-# INLINE sInteger #-}
sInteger :: Integer -> NumBits
sInteger = sIntegral . zigZag

{-# INLINE sNatural #-}
sNatural :: Natural -> NumBits
sNatural = sIntegral . toInteger

-- BAD: duplication of work with encoding
{-# INLINE sIntegral #-}
sIntegral :: (Bits t, Integral t) => t -> Int
sIntegral t =
  let vs = w7l t
   in length vs * 8

{-# INLINE sUTF8Max #-}
sUTF8Max :: Text -> NumBits
sUTF8Max (TI.Text _ _ lenInUnits) =
  let len =
#if MIN_VERSION_text(2,0,0)
        -- UTF-8 encoding, units are bytes
        lenInUnits
#else
        -- UTF-16 encoding, units are 16 bits words
        -- worst case: a utf-16 unit becomes a 3 bytes utf-8 encoding
        lenInUnits * 3
#endif
  in blobBits len

{-# INLINE sUTF16Max #-}
sUTF16Max :: T.Text -> NumBits
sUTF16Max (TI.Text _ _ lenInUnits) =
  let len =
#if MIN_VERSION_text(2,0,0)
        -- UTF-8 encoding
        -- worst case, a 1 byte UTF-8 char becomes a 2 bytes UTF-16 (ascii)
        lenInUnits * 2
#else
        -- UTF-16 encoding
        lenInUnits * 2
#endif
  in blobBits len

{-# INLINE sBytes #-}
sBytes :: B.ByteString -> NumBits
sBytes = blobBits . B.length

{-# INLINE sLazyBytes #-}
sLazyBytes :: L.ByteString -> NumBits
sLazyBytes bs = 16 + L.foldrChunks (\b l -> blkBitsBS b + l) 0 bs

{-# INLINE sShortBytes #-}
sShortBytes :: SBS.ShortByteString -> NumBits
sShortBytes = blobBits . SBS.length

{-# INLINE bitsToBytes #-}
bitsToBytes :: Int -> Int
bitsToBytes = numBlks 8

{-# INLINE numBlks #-}
numBlks :: Integral t => t -> t -> t
numBlks blkSize bits =
  let (d, m) = bits `divMod` blkSize
   in d +
      (if m == 0
         then 0
         else 1)

{-# INLINE arrayBits #-}
arrayBits :: Int -> NumBits
arrayBits = (8 *) . arrayChunks

{-# INLINE arrayChunks #-}
arrayChunks :: Int -> NumBits
arrayChunks = (1 +) . numBlks 255

{-# INLINE blobBits #-}
blobBits :: Int -> NumBits
blobBits numBytes =
  16 -- initial filler + final 0
   +
  blksBits numBytes

{-# INLINE blkBitsBS #-}
blkBitsBS :: B.ByteString -> NumBits
blkBitsBS = blksBits . B.length

{-# INLINE blksBits #-}
blksBits :: Int -> NumBits
blksBits numBytes = 8 * (numBytes + numBlks 255 numBytes)
