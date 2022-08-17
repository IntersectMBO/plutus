module Benches.Homogenous (
  benches
  ) where

import Data.Bits (zeroBits)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafeUseAsCStringLen)
import Data.Word (Word8)
import DataGen (mkHomogenousArg, noCleanup, sizes)
import Foreign.C.Types (CBool (CBool), CSize (CSize), CUChar)
import Foreign.Ptr (Ptr, castPtr)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, nfIO)

benches :: Benchmark
benches = bgroup "Basic homogeneity" $ benchBasic "Basic homogeneity" <$> sizes

-- Helpers

benchBasic ::
  String ->
  Int ->
  Benchmark
benchBasic mainLabel len =
  withResource (mkHomogenousArg len zeroBits) noCleanup $ \xs ->
    let naiveLabel = "all"
        cnaiveLabel = "naive C"
        cslidingLabel = "sliding window C"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> naiveLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench naiveLabel . nfIO $ BS.all (== zeroBits) <$> xs,
        bcompare matchLabel . bench cnaiveLabel . nfIO $ xs >>= wrapping (cHomogenousNaive zeroBits),
        bcompare matchLabel . bench cslidingLabel . nfIO $ xs >>= wrapping (cHomogenousSlidingWindow zeroBits)
        ]

-- Avoids having to rewrap C ops tediously each time
wrapping :: (Ptr CUChar -> CSize -> CBool) -> ByteString -> IO Bool
wrapping f bs = unsafeUseAsCStringLen bs $ \(ptr, len) -> do
  let (CBool res) = f (castPtr ptr) (fromIntegral len)
  pure $ res /= 0

foreign import ccall unsafe "cbits.h c_homogenous_naive"
  cHomogenousNaive ::
    Word8 ->
    Ptr CUChar ->
    CSize ->
    CBool

foreign import ccall unsafe "cbits.h c_homogenous_sliding_window"
  cHomogenousSlidingWindow ::
    Word8 ->
    Ptr CUChar ->
    CSize ->
    CBool
