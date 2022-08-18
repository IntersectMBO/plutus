-- editorconfig-checker-disable-file
module Implementations (
  rotateBS,
  rotateBSFast,
  ) where

import Control.Monad (void)
import Data.Bits (bit, rotate, zeroBits, (.&.), (.|.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafePackMallocCStringLen, unsafeUseAsCStringLen)
import Data.Foldable (foldl', for_)
import Data.Word (Word8)
import Foreign.C.Types (CSize)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.Storable (peek, poke)
import GHC.IO.Handle.Text (memcpy)
import System.IO.Unsafe (unsafeDupablePerformIO)

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
