{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE CPP                       #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}

-- |Strict encoder
module PlutusCore.Flat.Encoder.Strict where

import Control.Monad (when)
import Data.ByteString qualified as B
import Data.ByteString.Lazy qualified as L
import Data.Foldable
import PlutusCore.Flat.Encoder.Prim
import PlutusCore.Flat.Encoder.Size qualified as S
import PlutusCore.Flat.Encoder.Types
import PlutusCore.Flat.Memory
import PlutusCore.Flat.Types

-- import           Data.Semigroup
-- import           Data.Semigroup          (Semigroup (..))

#if !MIN_VERSION_base(4,11,0)
import Data.Semigroup (Semigroup (..))
#endif

#ifdef ETA_VERSION
-- import Data.Function(trampoline)
import GHC.IO (trampolineIO)
trampolineEncoding :: Encoding -> Encoding
trampolineEncoding (Encoding op) = Encoding (\s -> trampolineIO (op s))
#else

-- trampolineIO = id
#endif

-- |Strict encoder
strictEncoder :: NumBits -> Encoding -> B.ByteString
strictEncoder numBits enc =
  let (bs,numBitsUsed) = strictEncoderPartial numBits enc
      bitsInLastByte = numBitsUsed `mod` 8
  in if bitsInLastByte /=0
      then error $ unwords ["encoder: did not end on byte boundary, bits used in last byte=",show  bitsInLastByte]
      else bs

numEncodedBits :: Int -> Encoding -> NumBits
numEncodedBits numBits enc =snd $ strictEncoderPartial numBits enc

strictEncoderPartial ::
  Int                        -- ^ the maximum size in bits of the encoding
  -> Encoding                -- ^ the encoder
  -> (B.ByteString, NumBits) -- ^ the encoded bytestring + the actual number of encoded bits
strictEncoderPartial numBits (Encoding op)
  = let bufSize = S.bitsToBytes numBits
    in unsafeCreateUptoN' bufSize $ \ptr -> do
        S{..} <- op (S ptr 0 0)
        let numBitsUsed = nextPtr `minusPtr` ptr * 8 + usedBits
        when (numBitsUsed > numBits) $ error $ unwords ["encoder: size mismatch, expected <=",show numBits,"actual=",show numBitsUsed,"bits"]
        return (nextPtr `minusPtr` ptr,numBitsUsed)

newtype Encoding =
  Encoding
    { run :: Prim
    }

instance Show Encoding where
  show _ = "Encoding"

instance Semigroup Encoding where
  {-# INLINE (<>) #-}
  (<>) = encodingAppend

instance Monoid Encoding where
  {-# INLINE mempty #-}
  mempty = Encoding return

#if !(MIN_VERSION_base(4,11,0))
  {-# INLINE mappend #-}
  mappend = encodingAppend
#endif

  {-# INLINE mconcat #-}
  mconcat = foldl' mappend mempty

{-# INLINE encodingAppend #-}
encodingAppend :: Encoding -> Encoding -> Encoding
encodingAppend (Encoding f) (Encoding g) = Encoding m
    where
      m s@(S !_ !_ !_) = do
        !s1 <- f s
        g s1

-- PROB: GHC 8.02 won't always apply the rules leading to poor execution times (e.g. with lists)
-- TODO: check with newest GHC versions
{-# RULES
"encodersSN" forall h t . encodersS (h : t) =
             h `mappend` encodersS t
"encodersS0" encodersS [] = mempty
 #-}

{-# NOINLINE encodersS #-}
encodersS :: [Encoding] -> Encoding
-- Without the explicit parameter the rules won't fire!
encodersS ws = foldl' mappend mempty ws

sizeListWith :: (Foldable t1, Num t2) => (t3 -> t2 -> t2) -> t1 t3 -> t2 -> t2
sizeListWith size l sz = foldl' (\s e -> size e (s + 1)) (sz + 1) l
{-# INLINE sizeListWith #-}

-- encodersS ws = error $ unwords ["encodersS CALLED",show ws]
{-# INLINE encodeListWith #-}
-- |Encode as a List
encodeListWith :: (t -> Encoding) -> [t] -> Encoding
encodeListWith enc = go
  where
    go []     = eFalse
    go (x:xs) = eTrue <> enc x <> go xs

-- {-# INLINE encodeList #-}
-- encodeList :: (Foldable t, Flat a) => t a -> Encoding
-- encodeList l = F.foldl' (\acc a -> acc <> eTrue <> encode a) mempty l <> eFalse
-- {-# INLINE encodeList2 #-}
-- encodeList2 :: (Foldable t, Flat a) => t a -> Encoding
-- encodeList2 l = foldr (\a acc -> eTrue <> encode a <> acc) mempty l <> eFalse
{-# INLINE encodeArrayWith #-}
-- |Encode as Array
encodeArrayWith :: (t -> Encoding) -> [t] -> Encoding
encodeArrayWith _ [] = eWord8 0
encodeArrayWith f ws = Encoding $ go ws
  where
    go l s = do
      -- write a placeholder for the number of elements in current block
      s' <- eWord8F 0 s
      (n, sn, l) <- gol l 0 s'
      -- update actual number of elements
      s'' <- updateWord8 n s sn
      if null l
        then eWord8F 0 s''
        else go l s''
    -- encode up to 255 elements and returns (numberOfWrittenElements,elementsLeftToWrite,currentState)
    gol [] !n !s = return (n, s, [])
    gol l@(x:xs) !n !s
      | n == 255 = return (255, s, l)
      | otherwise = run (f x) s >>= gol xs (n + 1)

-- Encoding primitives
{-# INLINE eChar #-}
{-# INLINE eUTF8 #-}
{-# INLINE eNatural #-}
{-# INLINE eFloat #-}
{-# INLINE eDouble #-}
{-# INLINE eInteger #-}
{-# INLINE eInt64 #-}
{-# INLINE eInt32 #-}
{-# INLINE eInt16 #-}
{-# INLINE eInt8 #-}
{-# INLINE eInt #-}
{-# INLINE eWord64 #-}
{-# INLINE eWord32 #-}
{-# INLINE eWord16 #-}
{-# INLINE eWord8 #-}
{-# INLINE eWord #-}
{-# INLINE eBits #-}
{-# INLINE eFiller #-}
{-# INLINE eBool #-}
{-# INLINE eTrue #-}
{-# INLINE eFalse #-}
eChar :: Char -> Encoding
eChar = Encoding . eCharF

#if! defined (ETA_VERSION)
{-# INLINE eUTF16 #-}
eUTF16 :: Text -> Encoding
eUTF16 = Encoding . eUTF16F
#endif

eUTF8 :: Text -> Encoding
eUTF8 = Encoding . eUTF8F

eBytes :: B.ByteString -> Encoding
eBytes = Encoding . eBytesF

eLazyBytes :: L.ByteString -> Encoding
eLazyBytes = Encoding . eLazyBytesF

eShortBytes :: ShortByteString -> Encoding
eShortBytes = Encoding . eShortBytesF

eNatural :: Natural -> Encoding
eNatural = Encoding . eNaturalF

eFloat :: Float -> Encoding
eFloat = Encoding . eFloatF

eDouble :: Double -> Encoding
eDouble = Encoding . eDoubleF

eInteger :: Integer -> Encoding
eInteger = Encoding . eIntegerF

eInt64 :: Int64 -> Encoding
eInt64 = Encoding . eInt64F

eInt32 :: Int32 -> Encoding
eInt32 = Encoding . eInt32F

eInt16 :: Int16 -> Encoding
eInt16 = Encoding . eInt16F

eInt8 :: Int8 -> Encoding
eInt8 = Encoding . eInt8F

eInt :: Int -> Encoding
eInt = Encoding . eIntF

eWord64 :: Word64 -> Encoding
eWord64 = Encoding . eWord64F

eWord32 :: Word32 -> Encoding
eWord32 = Encoding . eWord32F

eWord16 :: Word16 -> Encoding
eWord16 = Encoding . eWord16F

eWord8 :: Word8 -> Encoding
eWord8 = Encoding . eWord8F

eWord :: Word -> Encoding
eWord = Encoding . eWordF

eBits16 :: NumBits -> Word16 -> Encoding
eBits16 n f = Encoding $ eBits16F n f

eBits :: NumBits -> Word8 -> Encoding
eBits n f = Encoding $ eBitsF n f

eFiller :: Encoding
eFiller = Encoding eFillerF

eBool :: Bool -> Encoding
eBool = Encoding . eBoolF

eTrue :: Encoding
eTrue = Encoding eTrueF

eFalse :: Encoding
eFalse = Encoding eFalseF

-- Size Primitives
-- Variable size
{-# INLINE vsize #-}
vsize :: (t -> NumBits) -> t -> NumBits -> NumBits
vsize !f !t !n = f t + n

-- Constant size
{-# INLINE csize #-}
csize :: NumBits -> t -> NumBits -> NumBits
csize !n _ !s = n + s

sChar :: Size Char
sChar = vsize S.sChar

sInt64 :: Size Int64
sInt64 = vsize S.sInt64

sInt32 :: Size Int32
sInt32 = vsize S.sInt32

sInt16 :: Size Int16
sInt16 = vsize S.sInt16

sInt8 :: Size Int8
sInt8 = csize S.sInt8

sInt :: Size Int
sInt = vsize S.sInt

sWord64 :: Size Word64
sWord64 = vsize S.sWord64

sWord32 :: Size Word32
sWord32 = vsize S.sWord32

sWord16 :: Size Word16
sWord16 = vsize S.sWord16

sWord8 :: Size Word8
sWord8 = csize S.sWord8

sWord :: Size Word
sWord = vsize S.sWord

sFloat :: Size Float
sFloat = csize S.sFloat

sDouble :: Size Double
sDouble = csize S.sDouble

sBytes :: Size B.ByteString
sBytes = vsize S.sBytes

sLazyBytes :: Size L.ByteString
sLazyBytes = vsize S.sLazyBytes

sShortBytes :: Size ShortByteString
sShortBytes = vsize S.sShortBytes

sNatural :: Size Natural
sNatural = vsize S.sNatural

sInteger :: Size Integer
sInteger = vsize S.sInteger

sUTF8Max :: Size Text
sUTF8Max = vsize S.sUTF8Max

sUTF16 :: Size Text
sUTF16 = vsize S.sUTF16Max

sFillerMax :: Size a
sFillerMax = csize S.sFillerMax

sBool :: Size Bool
sBool = csize S.sBool
