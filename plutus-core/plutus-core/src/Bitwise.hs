{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TupleSections      #-}

module Bitwise (
  integerToByteString,
  byteStringToInteger,
  andByteString,
  iorByteString,
  xorByteString,
  complementByteString,
  popCountByteString,
  testBitByteString,
  writeBitByteString,
  findFirstSetByteString,
  shiftByteString,
  rotateByteString,
  ) where

import Control.Monad (foldM_, unless)
import Data.Bits (FiniteBits, bit, complement, popCount, shiftL, shiftR, xor, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafePackMallocCStringLen, unsafeUseAsCString, unsafeUseAsCStringLen)
import Data.Foldable (foldl', for_)
import Data.Functor (void)
import Data.Kind (Type)
import Data.List.Split (chunksOf)
import Data.Text (Text, pack)
import Data.Word (Word64, Word8)
import Foreign.C.Types (CChar)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.Storable (Storable (peek, poke, sizeOf))
import GHC.Exts (fromList)
import GHC.IO.Handle.Text (memcpy)
import PlutusCore.Builtin.Emitter (Emitter, emit)
import PlutusCore.Evaluation.Result (EvaluationResult (EvaluationFailure))
import System.IO.Unsafe (unsafeDupablePerformIO)

{-# NOINLINE rotateByteString #-}
rotateByteString :: ByteString -> Integer -> ByteString
rotateByteString bs i = case magnitude `rem` bitLength of
  0 -> bs -- nothing to do irrespective of direction
  actualMagnitude -> case signum i of
    0 -> bs -- dummy case that never happens
    (-1) ->
      unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ decreasingRotation actualMagnitude
    _ ->
      unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ increasingRotation actualMagnitude
  where
    magnitude :: Int
    magnitude = fromIntegral . abs $ i
    bitLength :: Int
    bitLength = BS.length bs * 8
    decreasingRotation :: Int -> (Ptr CChar, Int) -> IO ByteString
    decreasingRotation actualMagnitude (src, len) = do
      let (bigShift, smallShift) = actualMagnitude `quotRem` 8
      dst <- mallocBytes len
      -- rotate over bytes
      for_ [0 .. len - 1] $ \srcIx -> do
        byte :: Word8 <- peek . plusPtr src $ srcIx
        let dstIx = (srcIx + bigShift) `mod` len
        poke (plusPtr dst dstIx) byte
      endByte :: Word8 <- peek . plusPtr src $ len - 1
      let mask = endByte `shiftL` (8 - smallShift)
      unless (smallShift == 0)
             (foldM_ (decreasingFixUp smallShift dst) mask [0 .. len - 1])
      unsafePackMallocCStringLen (dst, len)
    increasingRotation :: Int -> (Ptr CChar, Int) -> IO ByteString
    increasingRotation actualMagnitude (src, len) = do
      let (bigShift, smallShift) = actualMagnitude `quotRem` 8
      dst <- mallocBytes len
      for_ [0 .. len - 1] $ \srcIx -> do
        byte :: Word8 <- peek . plusPtr src $ srcIx
        let dstIx = (srcIx + len - bigShift) `mod` len
        poke (plusPtr dst dstIx) byte
      startByte :: Word8 <- peek . castPtr $ src
      let mask = startByte `shiftR` smallShift
      unless (smallShift == 0)
             (foldM_ (increasingFixUp smallShift dst) mask [len - 1, len - 2 .. 0])
      unsafePackMallocCStringLen (dst, len)

{-# NOINLINE shiftByteString #-}
shiftByteString :: ByteString -> Integer -> ByteString
shiftByteString bs i
  | magnitude >= bitLength = BS.replicate (BS.length bs) 0
  | otherwise = case signum i of
      0 -> bs
      (-1) ->
        unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ decreasingShift
      _ ->
        unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ increasingShift
  where
    magnitude :: Int
    magnitude = fromIntegral . abs $ i
    bitLength :: Int
    bitLength = BS.length bs * 8
    decreasingShift :: (Ptr CChar, Int) -> IO ByteString
    decreasingShift (src, len) = do
      let (bigShift, smallShift) = magnitude `quotRem` 8
      dst <- mallocBytes len
      -- clear the first bigShift bytes
      for_ [0 .. bigShift - 1] $ \j -> poke (plusPtr dst j) (0 :: CChar)
      -- copy in the rest, offset by bigShift
      void . memcpy (plusPtr dst bigShift) src . fromIntegral $ len - bigShift
      -- correct any outstanding shifts
      unless (smallShift == 0)
             (foldM_ (decreasingFixUp smallShift dst) 0 [bigShift .. len - 1])
      -- pack it all up and go
      unsafePackMallocCStringLen (dst, len)
    increasingShift :: (Ptr CChar, Int) -> IO ByteString
    increasingShift (src, len) = do
      let (bigShift, smallShift) = magnitude `quotRem` 8
      dst <- mallocBytes len
      -- copy in the last len - bigShift bytes, offset to start from 0
      void . memcpy dst (plusPtr src bigShift) . fromIntegral $ len - bigShift
      -- clear the rest
      for_ [len - bigShift, len - bigShift + 1 .. len - 1] $ \j -> poke (plusPtr dst j) (0 :: CChar)
      -- correct any outstanding shifts
      unless (smallShift == 0)
             (foldM_ (increasingFixUp smallShift dst) 0 [len - bigShift - 1, len - bigShift .. 0])
      -- pack it all up and go
      unsafePackMallocCStringLen (dst, len)

findFirstSetByteString :: ByteString -> Integer
findFirstSetByteString bs = foldl' go (-1) [0 .. len - 1]
  where
    go :: Integer -> Int -> Integer
    go acc ix
      | acc /= (-1) = acc -- we found one already
      | otherwise = case BS.index bs (len - ix - 1) of
          0  -> (-1) -- keep looking, nothing to find here
          w8 -> fromIntegral $ (ix * 8) + findPosition w8
    len :: Int
    len = BS.length bs

testBitByteString :: ByteString -> Integer -> Emitter (EvaluationResult Bool)
testBitByteString bs i
  | i < 0 || i >= bitLen = indexOutOfBoundsError "testBitByteString" bitLen i
  | otherwise = do
      let (bigOffset, smallOffset) = i `quotRem` 8
      let bigIx = fromIntegral $ byteLen - bigOffset - 1
      let mask = bit 0 `shiftL` fromIntegral smallOffset
      pure . pure $ case mask .&. BS.index bs bigIx of
        0 -> False
        _ -> True
  where
    byteLen :: Integer
    byteLen = fromIntegral . BS.length $ bs
    bitLen :: Integer
    bitLen = byteLen * 8

{-# NOINLINE writeBitByteString #-}
writeBitByteString :: ByteString -> Integer -> Bool -> Emitter (EvaluationResult ByteString)
writeBitByteString bs i b
  | i < 0 || i >= bitLen = indexOutOfBoundsError "writeBitByteString" bitLen i
  | otherwise = do
      let (bigOffset, smallOffset) = i `quotRem` 8
      let bigIx = fromIntegral $ byteLen - bigOffset - 1
      let mask = bit 0 `shiftL` fromIntegral smallOffset
      pure . pure . unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ go bigIx mask
  where
    byteLen :: Integer
    byteLen = fromIntegral . BS.length $ bs
    bitLen :: Integer
    bitLen = byteLen * 8
    go :: Int -> Word8 -> (Ptr CChar, Int) -> IO ByteString
    go bigIx mask (src, len) = do
      dst <- mallocBytes len
      void . memcpy dst src . fromIntegral $ len
      byte :: Word8 <- peek . plusPtr src $ bigIx
      let byte' = if b then mask .|. byte else complement mask .&. byte
      poke (castPtr . plusPtr src $ bigIx) byte'
      unsafePackMallocCStringLen (dst, len)

integerToByteString :: Integer -> ByteString
integerToByteString i = case signum i of
  0    -> BS.singleton 0
  (-1) -> twosComplement . integerToByteString . abs $ i
  _    -> fromList . intoBytes . toBitSequence $ i

byteStringToInteger :: ByteString -> Integer
byteStringToInteger bs = let len = BS.length bs in
  snd . foldl' go (1, 0) $ [len - 1, len - 2 .. 0]
  where
    go :: (Integer, Integer) -> Int -> (Integer, Integer)
    go (e, acc) ix = (e * 256, acc + e * (fromIntegral . BS.index bs $ ix))

{-# NOINLINE popCountByteString #-}
popCountByteString :: ByteString -> Integer
popCountByteString bs = unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ go
  where
    go :: (Ptr CChar, Int) -> IO Integer
    go (ptr, len) = do
      let (bigSteps, smallSteps) = len `quotRem` 8
      let bigPtr :: Ptr Word64 = castPtr ptr
      let smallPtr :: Ptr Word8 = castPtr . plusPtr ptr $ bigSteps * 8
      bigCount <- countBits bigPtr bigSteps
      smallCount <- countBits smallPtr smallSteps
      pure . fromIntegral $ bigCount + smallCount

{-# NOINLINE andByteString #-}
andByteString :: ByteString -> ByteString -> Emitter (EvaluationResult ByteString)
andByteString bs bs'
  | BS.length bs /= BS.length bs' = mismatchedLengthError "andByteString" bs bs'
  | otherwise = pure . pure . unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(ptr, len) ->
      unsafeUseAsCString bs' $ \ptr' ->
        zipBuild (.&.) ptr ptr' len >>= (unsafePackMallocCStringLen . (,len))

{-# NOINLINE iorByteString #-}
iorByteString :: ByteString -> ByteString -> Emitter (EvaluationResult ByteString)
iorByteString bs bs'
  | BS.length bs /= BS.length bs' = mismatchedLengthError "iorByteString" bs bs'
  | otherwise = pure . pure . unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(ptr, len) ->
      unsafeUseAsCString bs' $ \ptr' ->
        zipBuild (.|.) ptr ptr' len >>= (unsafePackMallocCStringLen . (,len))

{-# NOINLINE xorByteString #-}
xorByteString :: ByteString -> ByteString -> Emitter (EvaluationResult ByteString)
xorByteString bs bs'
  | BS.length bs /= BS.length bs' = mismatchedLengthError "xorByteString" bs bs'
  | otherwise = pure . pure . unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(ptr, len) ->
      unsafeUseAsCString bs' $ \ptr' ->
        zipBuild xor ptr ptr' len >>= (unsafePackMallocCStringLen . (,len))

{-# NOINLINE complementByteString #-}
complementByteString :: ByteString -> ByteString
complementByteString bs = unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(ptr, len) -> do
  resPtr <- mallocBytes len
  let (bigSteps, smallSteps) = len `quotRem` 8
  let bigDst :: Ptr Word64 = castPtr resPtr
  let smallDst :: Ptr Word8 = castPtr . plusPtr resPtr $ bigSteps * 8
  let bigSrc :: Ptr Word64 = castPtr ptr
  let smallSrc :: Ptr Word8 = castPtr . plusPtr ptr $ bigSteps * 8
  go bigDst bigSrc 0 bigSteps
  go smallDst smallSrc 0 smallSteps
  unsafePackMallocCStringLen (resPtr, len)
  where
    go :: forall (a :: Type) .
      (Storable a, FiniteBits a) =>
      Ptr a -> Ptr a -> Int -> Int -> IO ()
    go dst src offset lim
      | offset == lim = pure ()
      | otherwise = do
          let offset' = offset * sizeOf (undefined :: a)
          block :: a <- peek . plusPtr src $ offset'
          poke (plusPtr dst offset') . complement $ block
          go dst src (offset + 1) lim

-- Helpers

toBitSequence :: Integer -> [Bool]
toBitSequence i = go 0 (separateBit i) []
  where
    go :: Int -> Maybe (Integer, Bool) -> [Bool] -> [Bool]
    go len curr acc = case curr of
      Nothing -> case len `rem` 8 of
        0 -> acc
        _ -> go (len + 1) Nothing (False : acc)
      Just (d, b) -> go (len + 1) (separateBit d) (b : acc)

separateBit :: Integer -> Maybe (Integer, Bool)
separateBit i = case i of
  0 -> Nothing
  _ -> Just . fmap go $ i `quotRem` 2
    where
      go :: Integer -> Bool
      go = \case
        0 -> False
        _ -> True

intoBytes :: [Bool] -> [Word8]
intoBytes = fmap go . chunksOf 8
  where
    go :: [Bool] -> Word8
    go = \case
      [b7, b6, b5, b4, b3, b2, b1, b0] ->
        let b0Val = if b0 then 1 else 0
            b1Val = if b1 then 2 else 0
            b2Val = if b2 then 4 else 0
            b3Val = if b3 then 8 else 0
            b4Val = if b4 then 16 else 0
            b5Val = if b5 then 32 else 0
            b6Val = if b6 then 64 else 0
            b7Val = if b7 then 128 else 0 in
          b0Val + b1Val + b2Val + b3Val + b4Val + b5Val + b6Val + b7Val
      _ -> 0 -- should never happen

twosComplement :: ByteString -> ByteString
twosComplement bs = unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(ptr, len) -> do
  dst <- mallocBytes len
  let src :: Ptr Word8 = castPtr ptr
  go dst src 1 len False
  unsafePackMallocCStringLen (castPtr dst, len)
  where
    go :: Ptr Word8 -> Ptr Word8 -> Int -> Int -> Bool -> IO ()
    go dst src offset len added
      | offset > len = pure ()
      | otherwise = do
          w8 :: Word8 <- peek . plusPtr src $ len - offset
          if added
          then do
            poke (plusPtr dst $ len - offset) (complement w8)
            go dst src (offset + 1) len added
          else do
            let (added', w8') = computeAddByte w8
            poke (plusPtr dst $ len - offset) w8'
            go dst src (offset + 1) len added'

computeAddByte :: Word8 -> (Bool, Word8)
computeAddByte = \case
  0  -> (False, 0)
  w8 -> go 0 (False, 0) $ w8 `quotRem` 2
  where
    go :: Int -> (Bool, Word8) -> (Word8, Word8) -> (Bool, Word8)
    go step acc@(added, w8) (d, r)
      | step == 8 = acc
      | otherwise = let mask = bit 0 `shiftL` step
                        dr' = d `quotRem` 2 in
          if added
          then go (step + 1) (added, w8 `xor` mask) dr'
          else case r of
            0 -> go (step + 1) acc dr'
            _ -> go (step + 1) (True, w8 .|. mask) dr'

mismatchedLengthError :: forall (a :: Type) .
  Text ->
  ByteString ->
  ByteString ->
  Emitter (EvaluationResult a)
mismatchedLengthError loc bs bs' = do
  emit $ loc <> " failed"
  emit "Reason: mismatched argument lengths"
  emit $ "Length of first argument: " <> (pack . show . BS.length $ bs)
  emit $ "Length of second argument: " <> (pack . show . BS.length $ bs')
  pure EvaluationFailure

indexOutOfBoundsError :: forall (a :: Type) .
  Text ->
  Integer ->
  Integer ->
  Emitter (EvaluationResult a)
indexOutOfBoundsError loc lim i = do
  emit $ loc <> " failed"
  emit "Reason: out of bounds"
  emit $ "Attempted access at index " <> (pack . show $ i)
  emit $ "Valid indexes: from 0 to " <> (pack . show $ lim - 1)
  pure EvaluationFailure

zipBuild ::
  (forall (a :: Type) . (FiniteBits a, Storable a) => a -> a -> a) ->
  Ptr CChar ->
  Ptr CChar ->
  Int ->
  IO (Ptr CChar)
zipBuild f ptr ptr' len = do
  resPtr <- mallocBytes len
  let (bigSteps, smallSteps) = len `quotRem` 8
  let bigPtr :: Ptr Word64 = castPtr resPtr
  let smallPtr :: Ptr Word8 = castPtr . plusPtr resPtr $ bigSteps * 8
  go bigPtr (castPtr ptr) (castPtr ptr') 0 bigSteps
  let ptrRest :: Ptr Word8 = castPtr . plusPtr ptr $ bigSteps * 8
  let ptrRest' :: Ptr Word8 = castPtr . plusPtr ptr' $ bigSteps * 8
  go smallPtr ptrRest ptrRest' 0 smallSteps
  pure resPtr
  where
    go :: forall (b :: Type) .
      (FiniteBits b, Storable b) =>
      Ptr b ->
      Ptr b ->
      Ptr b ->
      Int ->
      Int ->
      IO ()
    go dst src src' offset lim
      | offset == lim = pure ()
      | otherwise = do
          let offset' = sizeOf (undefined :: b) * offset
          block :: b <- peek . plusPtr src $ offset'
          block' :: b <- peek . plusPtr src' $ offset'
          poke (plusPtr dst offset') (f block block')
          go dst src src' (offset + 1) lim

findPosition :: Word8 -> Int
findPosition w8 = foldl' go 7 . fmap (\i -> (i, bit 0 `shiftL` i)) $ [0 .. 7]
  where
    go :: Int -> (Int, Word8) -> Int
    go acc (i, mask) = case mask .&. w8 of
      0 -> acc -- nothing to see here, move along
      _ -> min acc i

decreasingFixUp :: Int -> Ptr CChar -> Word8 -> Int -> IO Word8
decreasingFixUp smallShift dst mask ix = do
  let ptr = plusPtr dst ix
  byte :: Word8 <- peek ptr
  let bitsWeCareAbout = byte `shiftR` smallShift
  let mask' = byte `shiftL` (8 - smallShift)
  let masked = bitsWeCareAbout .|. mask
  poke ptr masked
  pure mask'

increasingFixUp :: Int -> Ptr CChar -> Word8 -> Int -> IO Word8
increasingFixUp smallShift dst mask ix = do
  let ptr = plusPtr dst ix
  byte :: Word8 <- peek ptr
  let bitsWeCareAbout = byte `shiftL` smallShift
  let mask' = byte `shiftR` (8 - smallShift)
  let masked = bitsWeCareAbout .|. mask
  poke ptr masked
  pure mask'

countBits :: forall (a :: Type) .
  (FiniteBits a, Storable a) =>
  Ptr a -> Int -> IO Int
countBits ptr len = go 0 0
  where
    go :: Int -> Int -> IO Int
    go total offset
      | offset == len = pure total
      | otherwise = do
          let offset' = offset * sizeOf (undefined :: a)
          block :: a <- peek . plusPtr ptr $ offset'
          let total' = total + popCount block
          go total' (offset + 1)
