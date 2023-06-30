module Benches.Binary (
  benches
  ) where

import Control.Monad (guard)
import Data.Bits ((.&.))
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Internal (fromForeignPtr, mallocByteString)
import Data.ByteString.Unsafe (unsafeUseAsCStringLen)
import Data.Foldable (for_)
import Data.Word (Word8)
import DataGen (mkBinaryArgs, noCleanup, sizes)
import Foreign.C.Types (CSize (CSize), CUChar)
import Foreign.ForeignPtr (castForeignPtr, withForeignPtr)
import Foreign.Ptr (Ptr, castPtr)
import Foreign.Storable (peekByteOff, pokeByteOff)
import GHC.Exts (fromList)
import System.IO.Unsafe (unsafeDupablePerformIO)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, nfIO)

benches :: Benchmark
benches = bgroup "Basic AND" $ benchBasic "Basic AND" <$> sizes

-- Helpers

-- Benchmark a naive Haskell implementation against a clone of packZipWith and a
-- naive C one.
benchBasic ::
  String ->
  Int ->
  Benchmark
benchBasic mainLabel len =
  withResource (mkBinaryArgs len) noCleanup $ \xs ->
    let naiveLabel = "zipWith"
        packedLabel = "packedZipWith"
        cnaiveLabel = "naive C"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> naiveLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench naiveLabel . nfIO $ wrap usingZW <$> xs,
        bcompare matchLabel . bench packedLabel . nfIO $ wrap usingPZW <$> xs,
        bcompare matchLabel . bench cnaiveLabel . nfIO $ wrap usingCNaive <$> xs
        ]

-- Saves repeatedly doing the same thing
wrap ::
  (ByteString -> ByteString -> ByteString) ->
  (ByteString, ByteString) ->
  Maybe ByteString
wrap f (bs1, bs2) = do
  guard (BS.length bs2 == len)
  pure . f bs1 $ bs2
  where
    len :: Int
    len = BS.length bs1

usingZW :: ByteString -> ByteString -> ByteString
usingZW bs = fromList . BS.zipWith (.&.) bs

usingPZW :: ByteString -> ByteString -> ByteString
usingPZW bs1 bs2 = unsafeDupablePerformIO .
  unsafeUseAsCStringLen bs1 $ \(ptr1, len) ->
    unsafeUseAsCStringLen bs2 $ \(ptr2, _) -> do
      fp <- mallocByteString len
      withForeignPtr fp $ \dst -> for_ [0 .. len - 1] $ \i -> do
        b1 :: Word8 <- peekByteOff ptr1 i
        b2 <- peekByteOff ptr2 i
        pokeByteOff dst i $ b1 .&. b2
      pure . fromForeignPtr (castForeignPtr fp) 0 $ len

usingCNaive :: ByteString -> ByteString -> ByteString
usingCNaive bs1 bs2 = unsafeDupablePerformIO .
  unsafeUseAsCStringLen bs1 $ \(ptr1, len) ->
    unsafeUseAsCStringLen bs2 $ \(ptr2, _) -> do
      fp <- mallocByteString len
      withForeignPtr fp $ \dst ->
        cAndNaive dst (castPtr ptr1) (castPtr ptr2) (fromIntegral len)
      pure . fromForeignPtr (castForeignPtr fp) 0 $ len

foreign import ccall unsafe "cbits.h c_and_naive"
  cAndNaive ::
    Ptr CUChar ->
    Ptr CUChar ->
    Ptr CUChar ->
    CSize ->
    IO ()
