-- editorconfig-checker-disable-file
module Benches.Popcount (
  benches,
  cBenches
  ) where

import Data.Bits (popCount)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafeUseAsCStringLen)
import DataGen (mkUnaryArg, noCleanup, sizes)
import Foreign.C.Types (CSize (CSize), CUChar)
import Foreign.Ptr (Ptr, castPtr)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, nfIO)

benches :: Benchmark
benches = bgroup "Basic popcount" $ benchBasic "Basic popcount" <$> sizes

cBenches :: Benchmark
cBenches = bgroup "C popcount" $ benchC "C popcount" <$> sizes

-- Helpers

-- Benchmark a naive Haskell implementation against all the C ones
benchBasic ::
  String ->
  Int ->
  Benchmark
benchBasic mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let naiveLabel = "foldl'"
        cnaiveLabel = "naive C"
        cblockLabel = "block C"
        cblockUnrollLabel = "block unrolled C"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> naiveLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench naiveLabel . nfIO $ BS.foldl' (\acc w8 -> acc + popCount w8) 0 <$> xs,
        bcompare matchLabel . bench cnaiveLabel . nfIO $ xs >>= wrapping cPopcountNaive,
        bcompare matchLabel . bench cblockLabel . nfIO $ xs >>= wrapping cPopcountBlock,
        bcompare matchLabel . bench cblockUnrollLabel . nfIO $ xs >>= wrapping cPopcountBlockUnroll
        ]

-- Benchmark naive C against the other C ones
benchC ::
  String ->
  Int ->
  Benchmark
benchC mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let cnaiveLabel = "naive C"
        cblockLabel = "block C"
        cblockUnrollLabel = "block unrolled C"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> cnaiveLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench cnaiveLabel . nfIO $ xs >>= wrapping cPopcountNaive,
        bcompare matchLabel . bench cblockLabel . nfIO $ xs >>= wrapping cPopcountBlock,
        bcompare matchLabel . bench cblockUnrollLabel . nfIO $ xs >>= wrapping cPopcountBlockUnroll
        ]


-- Avoids having to rewrap C popcount ops tediously each time
wrapping :: (Ptr CUChar -> CSize -> CSize) -> ByteString -> IO CSize
wrapping f bs = unsafeUseAsCStringLen bs $ \(ptr, len) ->
  pure $ f (castPtr ptr) (fromIntegral len)

foreign import ccall unsafe "cbits.h c_popcount_naive"
  cPopcountNaive ::
    Ptr CUChar ->
    CSize ->
    CSize

foreign import ccall unsafe "cbits.h c_popcount_block"
  cPopcountBlock ::
    Ptr CUChar ->
    CSize ->
    CSize

foreign import ccall unsafe "cbits.h c_popcount_block_unroll"
  cPopcountBlockUnroll ::
    Ptr CUChar ->
    CSize ->
    CSize
