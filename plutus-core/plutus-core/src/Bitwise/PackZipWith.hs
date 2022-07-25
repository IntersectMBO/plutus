module Bitwise.PackZipWith (
  packZipWithBinary
  ) where

import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafePackMallocCStringLen, unsafeUseAsCStringLen)
import Data.Foldable (traverse_)
import Data.Word (Word8)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr, castPtr)
import Foreign.Storable (peekElemOff, pokeElemOff)
import System.IO.Unsafe (unsafeDupablePerformIO)

-- Replicate packZipWith from newer bytestring
-- the INLINE is their idea
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
