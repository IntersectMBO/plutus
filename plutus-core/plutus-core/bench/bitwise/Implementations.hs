{-# LANGUAGE BangPatterns     #-}
{-# LANGUAGE TypeApplications #-}

module Implementations (
  chunkZipWith2,
  chunkMap2,
  chunkMap3,
  chunkZipWith3,
  packZipWithBinary,
  chunkPopCount2,
  chunkPopCount3,
  rotateBS,
  rotateBSFast,
  ) where

import Control.Monad (foldM, void)
import Data.Bits (bit, popCount, rotate, zeroBits, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafePackMallocCStringLen, unsafeUseAsCStringLen)
import Data.Foldable (foldl', for_, traverse_)
import Data.WideWord.Word256 (Word256)
import Data.Word (Word64, Word8)
import Foreign.C.Types (CSize)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.Storable (peek, peekElemOff, poke, pokeElemOff, sizeOf)
import GHC.IO.Handle.Text (memcpy)
import System.IO.Unsafe (unsafeDupablePerformIO)

{-# INLINE chunkPopCount2 #-}
chunkPopCount2 :: ByteString -> Int
chunkPopCount2 bs = unsafeDupablePerformIO $ unsafeUseAsCStringLen bs $ \(src, len) -> do
  let bigStepSize = sizeOf @Word64 undefined
  let (bigSteps, smallSteps) = len `quotRem` bigStepSize
  !bigCount <- foldM (bigStep (castPtr src)) 0 [0 .. bigSteps - 1]
  let firstSmallPosition = bigSteps * bigStepSize
  foldM (smallStep (castPtr src)) bigCount [firstSmallPosition .. firstSmallPosition + smallSteps - 1]
  where
    bigStep :: Ptr Word64 -> Int -> Int -> IO Int
    bigStep src !acc offset = (acc +) . popCount <$> peekElemOff src offset
    smallStep :: Ptr Word8 -> Int -> Int -> IO Int
    smallStep src !acc offset = (acc +) . popCount <$> peekElemOff src offset

{-# INLINE chunkPopCount3 #-}
chunkPopCount3 :: ByteString -> Int
chunkPopCount3 bs = unsafeDupablePerformIO $ unsafeUseAsCStringLen bs $ \(src, len) -> do
  let bigStepSize = sizeOf @Word64 undefined
  let biggestStepSize = sizeOf @Word256 undefined
  let (biggestSteps, rest) = len `quotRem` biggestStepSize
  let (bigSteps, smallSteps) = rest `quotRem` bigStepSize
  !biggestCount <- foldM (biggestStep (castPtr src)) 0 [0 .. biggestSteps - 1]
  -- We now have to compute a Word64 offset corresponding to
  -- biggestSteps. This will be four times larger, as Word64 is
  -- one-quarter the width of a Word256.
  let firstBigPosition = biggestSteps * 4
  !bigCount <- foldM (bigStep (castPtr src))
                     biggestCount
                     [firstBigPosition .. firstBigPosition + bigSteps - 1]
  -- Same again, but now we have to multiply by 8 for similar reasons
  let firstSmallPosition = (firstBigPosition + bigSteps) * 8
  foldM (smallStep (castPtr src))
        bigCount
        [firstSmallPosition .. firstSmallPosition + smallSteps - 1]
  where
    biggestStep :: Ptr Word256 -> Int -> Int -> IO Int
    biggestStep src !acc offset = (acc +) . popCount <$> peekElemOff src offset
    bigStep :: Ptr Word64 -> Int -> Int -> IO Int
    bigStep src !acc offset = (acc +) . popCount <$> peekElemOff src offset
    smallStep :: Ptr Word8 -> Int -> Int -> IO Int
    smallStep src !acc offset = (acc +) . popCount <$> peekElemOff src offset

-- Replicate packZipWith from newer bytestring
{-# INLINE packZipWithBinary #-}
packZipWithBinary ::
  (Word8 -> Word8 -> Word8) ->
  ByteString ->
  ByteString ->
  Maybe ByteString
packZipWithBinary f bs bs'
  | BS.length bs /= BS.length bs' = Nothing
  | otherwise = pure go
  where
    go :: ByteString
    go = unsafeDupablePerformIO $
      unsafeUseAsCStringLen bs $ \(srcPtr, len) ->
        unsafeUseAsCStringLen bs' $ \(srcPtr', _) -> do
          dstPtr <- castPtr <$> mallocBytes len
          traverse_ (step (castPtr srcPtr) (castPtr srcPtr') dstPtr) [0 .. len - 1]
          unsafePackMallocCStringLen (castPtr dstPtr, len)
    step ::
      Ptr Word8 ->
      Ptr Word8 ->
      Ptr Word8 ->
      Int ->
      IO ()
    step src src' dst offset = do
      res <- f <$> peekElemOff src offset <*>
                   peekElemOff src' offset
      pokeElemOff dst offset res

-- For all the functionality below, all the function arguments must behave
-- identically on their respective inputs; essentially, the function arguments
-- should be the same function, modulo polymorphism.

{-# INLINE chunkMap2 #-}
chunkMap2 ::
  (Word8 -> Word8) ->
  (Word64 -> Word64) ->
  ByteString ->
  ByteString
chunkMap2 smallF bigF bs =
  unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(src, len) -> do
    dst <- mallocBytes len
    let bigStepSize = sizeOf @Word64 undefined
    let (bigSteps, smallSteps) = len `quotRem` bigStepSize
    traverse_ (bigStep (castPtr src) (castPtr dst)) [0 .. bigSteps - 1]
    let firstSmallPosition = bigSteps * bigStepSize
    traverse_ (smallStep (castPtr src) (castPtr dst))
              [firstSmallPosition, firstSmallPosition + 1 .. firstSmallPosition + smallSteps - 1]
    unsafePackMallocCStringLen (dst, len)
  where
    bigStep ::
      Ptr Word64 ->
      Ptr Word64 ->
      Int ->
      IO ()
    bigStep src dst offset =
      peekElemOff src offset >>= pokeElemOff dst offset . bigF
    smallStep ::
      Ptr Word8 ->
      Ptr Word8 ->
      Int ->
      IO ()
    smallStep src dst offset =
      peekElemOff src offset >>= pokeElemOff dst offset . smallF

{-# INLINE chunkMap3 #-}
chunkMap3 ::
  (Word8 -> Word8) ->
  (Word64 -> Word64) ->
  (Word256 -> Word256) ->
  ByteString ->
  ByteString
chunkMap3 smallF bigF biggestF bs =
  unsafeDupablePerformIO . unsafeUseAsCStringLen bs $ \(src, len) -> do
    dst <- mallocBytes len
    let bigStepSize = sizeOf @Word64 undefined
    let biggestStepSize = sizeOf @Word256 undefined
    let (biggestSteps, rest) = len `quotRem` biggestStepSize
    let (bigSteps, smallSteps) = rest `quotRem` bigStepSize
    traverse_ (biggestStep (castPtr src) (castPtr dst)) [0 .. biggestSteps - 1]
    let firstBigPosition = biggestSteps * 4
    traverse_ (bigStep (castPtr src) (castPtr dst))
              [firstBigPosition .. firstBigPosition + bigSteps - 1]
    let firstSmallPosition = (firstBigPosition + bigSteps) * 8
    traverse_ (smallStep (castPtr src) (castPtr dst))
              [firstSmallPosition .. firstSmallPosition + smallSteps - 1]
    unsafePackMallocCStringLen (dst, len)
  where
    biggestStep ::
      Ptr Word256 ->
      Ptr Word256 ->
      Int ->
      IO ()
    biggestStep src dst offset =
      peekElemOff src offset >>= pokeElemOff dst offset . biggestF
    bigStep ::
      Ptr Word64 ->
      Ptr Word64 ->
      Int ->
      IO ()
    bigStep src dst offset =
      peekElemOff src offset >>= pokeElemOff dst offset . bigF
    smallStep ::
      Ptr Word8 ->
      Ptr Word8 ->
      Int ->
      IO ()
    smallStep src dst offset =
      peekElemOff src offset >>= pokeElemOff dst offset . smallF

{-# INLINE chunkZipWith2 #-}
chunkZipWith2 ::
  (Word8 -> Word8 -> Word8) ->
  (Word64 -> Word64 -> Word64) ->
  ByteString ->
  ByteString ->
  Maybe ByteString
chunkZipWith2 smallF bigF bs bs'
  | BS.length bs /= BS.length bs' = Nothing
  | otherwise = pure go
  where
    go :: ByteString
    go = unsafeDupablePerformIO $
      unsafeUseAsCStringLen bs $ \(srcPtr, len) ->
        unsafeUseAsCStringLen bs' $ \(srcPtr', _) -> do
          dstPtr :: Ptr Word8 <- mallocBytes len
          let bigStepSize = sizeOf @Word64 undefined
          let (bigSteps, smallSteps) = len `quotRem` bigStepSize
          traverse_ (bigStep (castPtr srcPtr) (castPtr srcPtr') (castPtr dstPtr))
                    [0 .. bigSteps - 1]
          let firstSmallPosition = bigSteps * bigStepSize
          traverse_ (smallStep (castPtr srcPtr) (castPtr srcPtr') (castPtr dstPtr))
                    [firstSmallPosition, firstSmallPosition + 1 .. firstSmallPosition + smallSteps - 1]
          unsafePackMallocCStringLen (castPtr dstPtr, len)
    bigStep ::
      Ptr Word64 ->
      Ptr Word64 ->
      Ptr Word64 ->
      Int ->
      IO ()
    bigStep src src' dst offset = do
      res <- bigF <$> peekElemOff src offset <*>
                      peekElemOff src' offset
      pokeElemOff dst offset res
    smallStep ::
      Ptr Word8 ->
      Ptr Word8 ->
      Ptr Word8 ->
      Int ->
      IO ()
    smallStep src src' dst offset = do
      res <- smallF <$> peekElemOff src offset <*>
                        peekElemOff src' offset
      pokeElemOff dst offset res

{-# INLINE chunkZipWith3 #-}
chunkZipWith3 ::
  (Word8 -> Word8 -> Word8) ->
  (Word64 -> Word64 -> Word64) ->
  (Word256 -> Word256 -> Word256) ->
  ByteString ->
  ByteString ->
  Maybe ByteString
chunkZipWith3 smallF bigF biggestF bs bs'
  | BS.length bs /= BS.length bs' = Nothing
  | otherwise = pure go
  where
    go :: ByteString
    go = unsafeDupablePerformIO $
      unsafeUseAsCStringLen bs $ \(srcPtr, len) ->
        unsafeUseAsCStringLen bs' $ \(srcPtr', _) -> do
          dstPtr :: Ptr Word8 <- mallocBytes len
          let bigStepSize = sizeOf @Word64 undefined
          let biggestStepSize = sizeOf @Word256 undefined
          let (biggestSteps, rest) = len `quotRem` biggestStepSize
          let (bigSteps, smallSteps) = rest `quotRem` bigStepSize
          traverse_ (biggestStep (castPtr srcPtr) (castPtr srcPtr') (castPtr dstPtr))
                    [0 .. biggestSteps - 1]
          -- We now have to compute a Word64 offset corresponding to
          -- biggestSteps. This will be four times larger, as Word64 is
          -- one-quarter the width of a Word256.
          let firstBigPosition = biggestSteps * 4
          traverse_ (bigStep (castPtr srcPtr) (castPtr srcPtr') (castPtr dstPtr))
                    [firstBigPosition, firstBigPosition + 1 .. firstBigPosition + bigSteps - 1]
          -- Same again, but now we have to multiply by 8 for similar reasons.
          let firstSmallPosition = (firstBigPosition + bigSteps) * 8
          traverse_ (smallStep (castPtr srcPtr) (castPtr srcPtr') (castPtr dstPtr))
                    [firstSmallPosition, firstSmallPosition + 1 .. firstSmallPosition + smallSteps - 1]
          unsafePackMallocCStringLen (castPtr dstPtr, len)
    biggestStep ::
      Ptr Word256 ->
      Ptr Word256 ->
      Ptr Word256 ->
      Int ->
      IO ()
    biggestStep src src' dst offset = do
      res <- biggestF <$> peekElemOff src offset <*>
                          peekElemOff src' offset
      pokeElemOff dst offset res
    bigStep ::
      Ptr Word64 ->
      Ptr Word64 ->
      Ptr Word64 ->
      Int ->
      IO ()
    bigStep src src' dst offset = do
      res <- bigF <$> peekElemOff src offset <*>
                      peekElemOff src' offset
      pokeElemOff dst offset res
    smallStep ::
      Ptr Word8 ->
      Ptr Word8 ->
      Ptr Word8 ->
      Int ->
      IO ()
    smallStep src src' dst offset = do
      res <- smallF <$> peekElemOff src offset <*>
                        peekElemOff src' offset
      pokeElemOff dst offset res

-- Clone of rotation logic without any prechecks
rotateBS :: ByteString -> Int -> ByteString
rotateBS bs i = case i `rem` bitLen of
  0         -> bs
  magnitude -> overPtrLen bs $ \ptr len -> go ptr len magnitude
  where
    bitLen :: Int
    bitLen = BS.length bs * 8
    go :: Ptr Word8 -> Int -> Int -> IO (Ptr Word8)
    go _ len displacement = do
      dst <- mallocBytes len
      for_ [0 .. len - 1] $ \j -> do
        let start = (len - 1 - j) * 8
        let dstByte = foldl' (addBit start displacement) zeroBits [0 .. 7]
        poke (plusPtr dst j) dstByte
      pure dst
    addBit :: Int -> Int -> Word8 -> Int -> Word8
    addBit start displacement acc offset =
      let oldIx = (offset + start + bitLen - displacement) `rem` bitLen in
        if dangerousRead bs oldIx
        then acc .|. bit offset
        else acc

-- Precheck and block optimizations
rotateBSFast :: ByteString -> Int -> ByteString
rotateBSFast bs i = case i `rem` bitLen of
  0         -> bs
  magnitude -> overPtrLen bs $ \ptr len -> go ptr len magnitude
  where
    bitLen :: Int
    bitLen = BS.length bs * 8
    go :: Ptr Word8 -> Int -> Int -> IO (Ptr Word8)
    go src len displacement = do
      dst <- mallocBytes len
      case len of
        -- If we only have one byte, we an borrow from the Bits instance for
        -- Word8.
        1 -> do
          srcByte <- peek src
          let srcByte' = srcByte `rotate` displacement
          poke dst srcByte'
        -- If we rotate by a multiple of 8, we only need to move around whole
        -- bytes, rather than individual bits. Because we only move contiguous
        -- blocks (regardless of rotation direction), we can do this using
        -- memcpy, which is must faster, especially on larger ByteStrings.
        _ -> case displacement `quotRem` 8 of
          (bigMove, 0) -> do
            let mainLen :: CSize = fromIntegral . abs $ bigMove
            let restLen :: CSize = fromIntegral len - mainLen
            void $ case signum bigMove of
              1 -> memcpy (plusPtr dst . fromIntegral $ restLen) src mainLen >>
                   memcpy dst (plusPtr src . fromIntegral $ mainLen) restLen
              _ -> memcpy (plusPtr dst . fromIntegral $ mainLen) src restLen >>
                   memcpy dst (plusPtr src . fromIntegral $ restLen) mainLen
          -- If we don't rotate by a multiple of 8, we have to construct new
          -- bytes, rather than just copying over old ones. We do this in two
          -- steps:
          --
          -- 1. Compute the 'read offset' into the source ByteString based on
          -- the rotation magnitude and direction.
          -- 2. Use that read offset to perform an (unchecked) bit lookup for an
          -- entire 8-bit block, then construct the byte that results.
          --
          -- We can do the bytes in the result in any order using this method:
          -- we choose to do it in traversal order.
          _ -> for_ [0 .. len - 1] $ \j -> do
                let start = (len - 1 - j) * 8
                let dstByte = foldl' (addBit start displacement) zeroBits [0 .. 7]
                poke (plusPtr dst j) dstByte
      pure dst
    addBit :: Int -> Int -> Word8 -> Int -> Word8
    addBit start displacement acc offset =
      let oldIx = (offset + start + bitLen - displacement) `rem` bitLen in
        if dangerousRead bs oldIx
        then acc .|. bit offset
        else acc

-- Helpers

overPtrLen :: ByteString -> (Ptr Word8 -> Int -> IO (Ptr Word8)) -> ByteString
overPtrLen bs f = unsafeDupablePerformIO . unsafeUseAsCStringLen bs $
  \(ptr, len) -> f (castPtr ptr) len >>= \p ->
    unsafePackMallocCStringLen (castPtr p, len)

dangerousRead :: ByteString -> Int -> Bool
dangerousRead bs i =
  let (bigOffset, smallOffset) = i `quotRem` 8
      bigIx = BS.length bs - bigOffset - 1
      mask = bit smallOffset in
    case mask .&. BS.index bs bigIx of
      0 -> False
      _ -> True
