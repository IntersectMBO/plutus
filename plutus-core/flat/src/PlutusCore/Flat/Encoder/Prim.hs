{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |Encoding Primitives
module PlutusCore.Flat.Encoder.Prim
  (
    -- Primitives whose name starts with 'e' encode a value in place
    eBits16F
  , eBitsF
  , eFloatF
  , eDoubleF
#if ! defined (ETA_VERSION)
  , eUTF16F
#endif
  , eUTF8F
  , eCharF
  , eNaturalF
  , eIntegerF
  , eInt64F
  , eInt32F
  , eIntF
  , eInt16F
  , eInt8F
  , eWordF
  , eWord64F
  , eWord32F
  , eWord16F
  , eBytesF
  , eLazyBytesF
  , eShortBytesF
  , eWord8F
  , eFillerF
  , eBoolF
  , eTrueF
  , eFalseF

  , varWordF

  , updateWord8
  , w7l

    -- * Exported for testing only
  , eWord32BEF
  , eWord64BEF
  , eWord32E
  , eWord64E
  ) where

import Control.Monad
import Data.ByteString qualified as B
import Data.ByteString.Lazy qualified as L
import Data.ByteString.Lazy.Internal qualified as L
import Data.ByteString.Short.Internal qualified as SBS
import Data.Char
import Data.Primitive.ByteArray
import Data.Text qualified as T
import PlutusCore.Flat.Data.FloatCast
import PlutusCore.Flat.Encoder.Types
import PlutusCore.Flat.Endian
import PlutusCore.Flat.Memory
import PlutusCore.Flat.Types

#if ! defined (ETA_VERSION) && ! MIN_VERSION_text(2,0,0)
import Data.Text.Array qualified as TA
import Data.Text.Internal qualified as TI
-- import           Data.FloatCast
-- import           Data.Primitive.ByteArray
-- import qualified Data.Text                      as T
#endif
import Data.Text.Encoding qualified as TE
import Foreign
import PlutusCore.Flat.Data.ZigZag
-- import Debug.Trace
#include "MachDeps.h"
-- traceShowId :: a -> a
-- traceShowId = id

-- $setup
-- >>> import PlutusCore.Flat.Instances.Test
-- >>> import PlutusCore.Flat.Bits
-- >>> import PlutusCore.Flat.Encoder.Strict
-- >>> import Control.Monad
-- >>> let enc e = prettyShow $ encBits 256 (Encoding e)

{-# INLINE eFloatF #-}
eFloatF :: Float -> Prim
eFloatF = eWord32BEF . floatToWord

{-# INLINE eDoubleF #-}
eDoubleF :: Double -> Prim
eDoubleF = eWord64BEF . doubleToWord

{-# INLINE eWord64BEF #-}
eWord64BEF :: Word64 -> Prim
eWord64BEF = eWord64E toBE64

{-# INLINE eWord32BEF #-}
eWord32BEF :: Word32 -> Prim
eWord32BEF = eWord32E toBE32

{-# INLINE eCharF #-}
eCharF :: Char -> Prim
eCharF = eWord32F . fromIntegral . ord

{-# INLINE eWordF #-}
eWordF :: Word -> Prim
{-# INLINE eIntF #-}
eIntF :: Int -> Prim

#if WORD_SIZE_IN_BITS == 64
eWordF = eWord64F . (fromIntegral :: Word -> Word64)

eIntF = eInt64F . (fromIntegral :: Int -> Int64)
#elif WORD_SIZE_IN_BITS == 32
eWordF = eWord32F . (fromIntegral :: Word -> Word32)

eIntF = eInt32F . (fromIntegral :: Int -> Int32)
#else
#error expected WORD_SIZE_IN_BITS to be 32 or 64
#endif

{-# INLINE eInt8F #-}
eInt8F :: Int8 -> Prim
eInt8F = eWord8F . zigZag

{-# INLINE eInt16F #-}
eInt16F :: Int16 -> Prim
eInt16F = eWord16F . zigZag

{-# INLINE eInt32F #-}
eInt32F :: Int32 -> Prim
eInt32F = eWord32F . zigZag

{-# INLINE eInt64F #-}
eInt64F :: Int64 -> Prim
eInt64F = eWord64F . zigZag

{-# INLINE eIntegerF #-}
eIntegerF :: Integer -> Prim
eIntegerF = eIntegralF . zigZag

{-# INLINE eNaturalF #-}
eNaturalF :: Natural -> Prim
eNaturalF = eIntegralF . toInteger

{-# INLINE eIntegralF #-}
eIntegralF :: (Bits t, Integral t) => t -> Prim
eIntegralF t =
  let vs = w7l t
   in eIntegralW vs

w7l :: (Bits t, Integral t) => t -> [Word8]
w7l t =
  let l = low7 t
      t' = t `unsafeShiftR` 7
   in if t' == 0
        then [l]
        else w7 l : w7l t'
  where
    {-# INLINE w7 #-}
    --lowByte :: (Bits t, Num t) => t -> Word8
    w7 :: Word8 -> Word8
    w7 l = l .|. 0x80

-- | Encoded as: data NonEmptyList = Elem Word7 | Cons Word7 List
{-# INLINE eIntegralW #-}
eIntegralW :: [Word8] -> Prim
eIntegralW vs s@(S op _ o)
  | o == 0 = foldM pokeWord' op vs >>= \op' -> return (S op' 0 0)
  | otherwise = foldM (flip eWord8F) s vs

{-
>>> enc $ \s0 -> eTrueF s0 >>= \s1 -> eWord8F 0 s1 >>= \s2 -> eTrueF s2
"10000000 01"
-}

{-# INLINE eWord8F #-}
eWord8F :: Word8 -> Prim
eWord8F t s@(S op _ o)
  | o == 0 = pokeWord op t
  | otherwise = eByteUnaligned t s

{-# INLINE eWord32E #-}
eWord32E :: (Word32 -> Word32) -> Word32 -> Prim
eWord32E conv t (S op w o)
  | o == 0 = pokeW conv op t >> skipBytes op 4
  | otherwise =
    pokeW conv op (asWord32 w `unsafeShiftL` 24 .|. t `unsafeShiftR` o) >>
    return (S (plusPtr op 4) (asWord8 t `unsafeShiftL` (8 - o)) o)

{-# INLINE eWord64E #-}
eWord64E :: (Word64 -> Word64) -> Word64 -> Prim
eWord64E conv t (S op w o)
  | o == 0 = poke64 conv op t >> skipBytes op 8
  | otherwise =
    poke64 conv op (asWord64 w `unsafeShiftL` 56 .|. t `unsafeShiftR` o) >>
    return (S (plusPtr op 8) (asWord8 t `unsafeShiftL` (8 - o)) o)

{-# INLINE eWord16F #-}
eWord16F :: Word16 -> Prim
eWord16F = varWordF

{-# INLINE eWord32F #-}
eWord32F :: Word32 -> Prim
eWord32F = varWordF

{-# INLINE eWord64F #-}
eWord64F :: Word64 -> Prim
eWord64F = varWordF

{-# INLINE varWordF #-}
varWordF :: (Bits t, Integral t) => t -> Prim
varWordF t s@(S _ _ o)
  | o == 0 = varWord eByteAligned t s
  | otherwise = varWord eByteUnaligned t s

{-# INLINE varWord #-}
varWord :: (Bits t, Integral t) => (Word8 -> Prim) -> t -> Prim
varWord writeByte t s
  | t < 128 = writeByte (fromIntegral t) s
  | t < 16384 = varWord2_ writeByte t s
  | t < 2097152 = varWord3_ writeByte t s
  | otherwise = varWordN_ writeByte t s
  where
    {-# INLINE varWord2_ #-}
      -- TODO: optimise, using a single Write16?
    varWord2_ writeByte t s =
      writeByte (fromIntegral t .|. 0x80) s >>=
      writeByte (fromIntegral (t `unsafeShiftR` 7) .&. 0x7F)
    {-# INLINE varWord3_ #-}
    varWord3_ writeByte t s =
      writeByte (fromIntegral t .|. 0x80) s >>=
      writeByte (fromIntegral (t `unsafeShiftR` 7) .|. 0x80) >>=
      writeByte (fromIntegral (t `unsafeShiftR` 14) .&. 0x7F)

-- {-# INLINE varWordN #-}
varWordN_ :: (Bits t, Integral t) => (Word8 -> Prim) -> t -> Prim
varWordN_ writeByte = go
  where
    go !v !st =
      let !l = low7 v
          !v' = v `unsafeShiftR` 7
       in if v' == 0
            then writeByte l st
            else writeByte (l .|. 0x80) st >>= go v'

{-# INLINE low7 #-}
low7 :: (Integral a) => a -> Word8
low7 t = fromIntegral t .&. 0x7F

-- | Encode text as UTF8 and encode the result as an array of bytes
eUTF8F :: T.Text -> Prim
eUTF8F = eBytesF . TE.encodeUtf8

-- | Encode text as UTF16 and encode the result as an array of bytes
#if ! defined (ETA_VERSION)
eUTF16F :: T.Text -> Prim
#if MIN_VERSION_text(2,0,0)
eUTF16F = eBytesF . TE.encodeUtf16LE
#else
eUTF16F t = eFillerF >=> eUTF16F_ t
  where
    eUTF16F_ (TI.Text (TA.Array array) w16Off w16Len) s =
      writeArray array (2 * w16Off) (2 * w16Len) (nextPtr s)
#endif
#endif

-- |Encode a Lazy ByteString
eLazyBytesF :: L.ByteString -> Prim
eLazyBytesF bs = eFillerF >=> \s -> write bs (nextPtr s)
    -- Single copy
  where
    write lbs op = do
      case lbs of
        L.Chunk h t -> writeBS h op >>= write t
        L.Empty     -> pokeWord op 0

{-# INLINE eShortBytesF #-}
eShortBytesF :: SBS.ShortByteString -> Prim
eShortBytesF bs = eFillerF >=> eShortBytesF_ bs
  where
    eShortBytesF_ :: SBS.ShortByteString -> Prim
    eShortBytesF_ bs@(SBS.SBS arr) (S op _ 0) = writeArray arr 0 (SBS.length bs) op
    eShortBytesF_ _ _                         = error "impossible"

-- data Array a = Array0 | Array1 a ... | Array255 ...
writeArray :: ByteArray# -> Int -> Int -> Ptr Word8 -> IO S
writeArray arr soff slen sop = do
  op' <- go soff slen sop
  pokeWord op' 0
  where
    go !off !len !op
      | len == 0 = return op
      | otherwise =
        let l = min 255 len
         in pokeWord' op (fromIntegral l) >>= pokeByteArray arr off l >>=
            go (off + l) (len - l)

eBytesF :: B.ByteString -> Prim
eBytesF bs = eFillerF >=> eBytesF_
  where
    eBytesF_ s = do
      op' <- writeBS bs (nextPtr s)
      pokeWord op' 0

-- |Encode up to 9 bits
{-# INLINE eBits16F #-}
eBits16F :: NumBits -> Word16 -> Prim
--eBits16F numBits code | numBits >8 = eBitsF (numBits-8) (fromIntegral $ code `unsafeShiftR` 8) >=> eBitsF 8 (fromIntegral code)
-- eBits16F _ _ = eFalseF
eBits16F 9 code =
  eBitsF 1 (fromIntegral $ code `unsafeShiftR` 8) >=>
  eBitsF_ 8 (fromIntegral code)
eBits16F numBits code = eBitsF numBits (fromIntegral code)

-- |Encode up to 8 bits.
{-# INLINE eBitsF #-}
eBitsF :: NumBits -> Word8 -> Prim
eBitsF 1 0 = eFalseF
eBitsF 1 1 = eTrueF
eBitsF 2 0 = eFalseF >=> eFalseF
eBitsF 2 1 = eFalseF >=> eTrueF
eBitsF 2 2 = eTrueF >=> eFalseF
eBitsF 2 3 = eTrueF >=> eTrueF
eBitsF n t = eBitsF_ n t

{-
eBits Example:
Before:
n = 6
t = 00.101011
o = 3
w = 111.00000

After:
[ptr] = w(111)t(10101)
w' = t(1)0000000
o'= 1

o'=3+6=9
f = 8-9 = -1
o'' = 1
8-o''=7

if n=8,o=3:
o'=11
f=8-11=-3
o''=3
8-o''=5
-}
-- {-# NOINLINE eBitsF_ #-}
eBitsF_ :: NumBits -> Word8 -> Prim
eBitsF_ n t (S op w o) =
    let o' = o + n -- used bits
        f = 8 - o' -- remaining free bits
     in if | f > 0 -> return $ S op (w .|. (t `unsafeShiftL` f)) o'
           | f == 0 -> pokeWord op (w .|. t)
           | otherwise ->
             let o'' = -f
              in poke op (w .|. (t `unsafeShiftR` o'')) >>
                 return (S (plusPtr op 1) (t `unsafeShiftL` (8 - o'')) o'')

{-# INLINE eBoolF #-}
eBoolF :: Bool -> Prim
eBoolF False = eFalseF
eBoolF True  = eTrueF

-- | >>> enc eTrueF
-- "1"
{-# INLINE eTrueF #-}
eTrueF :: Prim
eTrueF (S op w o)
  | o == 7 = pokeWord op (w .|. 1)
  | otherwise = return (S op (w .|. 128 `unsafeShiftR` o) (o + 1))

-- | >>> enc eFalseF
-- "0"
{-# INLINE eFalseF #-}
eFalseF :: Prim
eFalseF (S op w o)
  | o == 7 = pokeWord op w
  | otherwise = return (S op w (o + 1))

{- |

>>> enc $ eTrueF >=> eFillerF
"10000001"

>>> enc eFillerF
"00000001"
-}
{-# INLINE eFillerF #-}
eFillerF :: Prim
eFillerF (S op w _) = pokeWord op (w .|. 1)

-- {-# INLINE poke16 #-}
-- TODO TEST
-- poke16 :: Word16 -> Prim
-- poke16 t (S op w o) | o == 0 = poke op w >> skipBytes op 2
{-
To be used only when usedBits /= 0

>>> enc (eFalseF >=> eFalseF >=> eByteUnaligned 255)
"00111111 11"
-}
{-# INLINE eByteUnaligned #-}
eByteUnaligned :: Word8 -> Prim
eByteUnaligned t (S op w o) =
  poke op (w .|. (t `unsafeShiftR` o)) >>
  return (S (plusPtr op 1) (t `unsafeShiftL` (8 - o)) o)

{- To be used only when usedBits = 0

>>> enc (eFalseF >=> eFalseF >=> eFalseF >=> eByteAligned 255)
"11111111"
-}
{-# INLINE eByteAligned #-}
eByteAligned :: Word8 -> Prim
eByteAligned t (S op _ _) = pokeWord op t

{-|
>>> enc $ \s-> eWord8F 0 s >>= updateWord8 255 s
"11111111"

>>> enc $ \s0 -> eTrueF s0 >>= \s1 -> eWord8F 255 s1 >>= eWord8F 255 >>= updateWord8 0 s1
"10000000 01111111 1"

>>> enc $ \s0 -> eFalseF s0 >>= \s1 -> eWord8F 0 s1 >>= updateWord8 255 s1
"01111111 1"

>>> enc $ \s0 -> eFalseF s0 >>= \s1 -> eWord8F 0 s1 >>= updateWord8 255 s1 >>= eFalseF
"01111111 10"

>>> enc $ \s0 -> eTrueF s0 >>= \s1 -> eWord8F 255 s1 >>= eTrueF >>= updateWord8 0 s1 >>= eTrueF
"10000000 011"

@since 0.5
-}
updateWord8 :: Word8 -> S -> Prim
updateWord8 t mem s = do
  uncache s
  pokeWord8 t mem
  cache s

uncache :: S -> IO ()
uncache s = poke (nextPtr s) (currByte s)

cache :: Prim
cache s = do
  w <- (mask s .&.) <$> peek (nextPtr s)
  return $ s {currByte = w}

mask :: S -> Word8
mask s = 255 `unsafeShiftL` (8 - usedBits s)

{-# INLINE pokeWord8 #-}
pokeWord8 :: Word8 -> S -> IO ()
pokeWord8 t  (S op _ 0) = poke op t
pokeWord8 t  (S op w o) = do
        poke op (w .|. (t `unsafeShiftR` o))
        let op' :: Ptr Word8 = plusPtr op 1
        v :: Word8 <- peek op'
        poke op' (t `unsafeShiftL` (8 - o) .|. ((v `unsafeShiftL` o) `unsafeShiftR` o))

-- | o == 0 = pokeByteAligned t s
-- | otherwise = pokeByteUnaligned t s
--   where
-- {-# INLINE pokeByteUnaligned #-}
-- pokeByteUnaligned :: Word8 -> S -> IO ()
-- pokeByteUnaligned t (S op w o) = do
--   let op' = plusPtr op 1
--   poke op (w .|. (t `unsafeShiftR` o))
--   v :: Word8 <- peek op'
--   poke op' (t `unsafeShiftL` (8 - o) .|. ((v `unsafeShiftL` o) `unsafeShiftR` o))

-- {-# INLINE pokeByteAligned #-}
-- pokeByteAligned :: Word8 -> S -> IO ()
-- pokeByteAligned t (S op _ _) = poke op t

-- FIX: not really pokes

{-# INLINE pokeWord #-}
pokeWord :: Storable a => Ptr a -> a -> IO S
pokeWord op w = poke op w >> skipByte op

{-# INLINE pokeWord' #-}
pokeWord' :: Storable a => Ptr a -> a -> IO (Ptr b)
pokeWord' op w = poke op w >> return (plusPtr op 1)

{-# INLINE pokeW #-}
pokeW :: Storable a => (t -> a) -> Ptr a1 -> t -> IO ()
pokeW conv op t = poke (castPtr op) (conv t)

{-# INLINE poke64 #-}
poke64 :: (t -> Word64) -> Ptr a -> t -> IO ()
poke64 conv op t = poke (castPtr op) (conv t)
-- poke64 conv op t = poke (castPtr op) (fix64 . conv $ t)

{-# INLINE skipByte #-}
skipByte :: Monad m => Ptr a -> m S
skipByte op = return (S (plusPtr op 1) 0 0)

{-# INLINE skipBytes #-}
skipBytes :: Monad m => Ptr a -> Int -> m S
skipBytes op n = return (S (plusPtr op n) 0 0)

--{-# INLINE nextByteW #-}
--nextByteW op w = return (S (plusPtr op 1) 0 0)
writeBS :: B.ByteString -> Ptr Word8 -> IO (Ptr Word8)
writeBS bs op -- @(BS.PS foreignPointer sourceOffset sourceLength) op
  | B.length bs == 0 = return op
  | otherwise =
    let (h, t) = B.splitAt 255 bs
     in pokeWord' op (fromIntegral $ B.length h :: Word8) >>= pokeByteString h >>=
        writeBS t
    -- 2X slower (why?)
    -- withForeignPtr foreignPointer goS
    --   where
    --     goS sourcePointer = go op (sourcePointer `plusPtr` sourceOffset) sourceLength
    --       where
    --         go !op !off !len | len == 0 = return op
    --                          | otherwise = do
    --                           let l = min 255 len
    --                           op' <- pokeWord' op (fromIntegral l)
    --                           BS.memcpy op' off l
    --                           go (op' `plusPtr` l) (off `plusPtr` l) (len-l)

{-# INLINE asWord64 #-}
asWord64 :: Integral a => a -> Word64
asWord64 = fromIntegral

{-# INLINE asWord32 #-}
asWord32 :: Integral a => a -> Word32
asWord32 = fromIntegral

{-# INLINE asWord8 #-}
asWord8 :: Integral a => a -> Word8
asWord8 = fromIntegral
