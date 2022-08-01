{-# LANGUAGE TypeApplications #-}

module Bitwise.ChunkZipWith (
  chunkZipWith2
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafePackMallocCStringLen, unsafeUseAsCStringLen)
import Data.Foldable (traverse_)
import Data.Word (Word64, Word8)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr, castPtr)
import Foreign.Storable (peekElemOff, pokeElemOff, sizeOf)
import System.IO.Unsafe (unsafeDupablePerformIO)

-- We must ensure that both function arguments behave identically on their
-- respective inputs. Essentially, the two function arguments should be the same
-- function.
{-# NOINLINE chunkZipWith2 #-}
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
