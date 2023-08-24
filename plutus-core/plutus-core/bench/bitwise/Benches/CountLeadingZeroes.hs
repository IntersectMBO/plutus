module Benches.CountLeadingZeroes (
  benches,
  cBenches,
  ) where

import Data.Bits (countLeadingZeros, zeroBits)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafeUseAsCStringLen)
import Data.Maybe (fromMaybe)
import DataGen (mkZeroesOne, noCleanup, sizes)
import Foreign.C.Types (CSize (CSize), CUChar)
import Foreign.Ptr (Ptr, castPtr)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, nfIO)

benches :: Benchmark
benches = bgroup "Basic CLZ" $ benchBasic "CLZ" <$> sizes

cBenches :: Benchmark
cBenches = bgroup "C CLZ" $ benchC "C CLZ" <$> sizes

-- Helpers

benchBasic ::
  String ->
  Int ->
  Benchmark
benchBasic mainLabel len =
  withResource (mkZeroesOne len) noCleanup $ \xs ->
    let naiveLabel = "ByteString ops"
        cnaiveLabel = "naive C"
        cblockLabel = "block C"
        cunrolledLabel = "unrolled C"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> naiveLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench naiveLabel . nfIO $ naiveClz <$> xs,
        bcompare matchLabel . bench cnaiveLabel . nfIO $ xs >>= wrapping cClzNaive,
        bcompare matchLabel . bench cblockLabel . nfIO $ xs >>= wrapping cClzBlock,
        bcompare matchLabel . bench cunrolledLabel . nfIO $ xs >>= wrapping cClzBlockUnrolled
      ]

benchC ::
  String ->
  Int ->
  Benchmark
benchC mainLabel len =
  withResource (mkZeroesOne len) noCleanup $ \xs ->
    let cnaiveLabel = "naive C"
        cblockLabel = "block C"
        cunrolledLabel = "unrolled C"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> cnaiveLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench cnaiveLabel . nfIO $ xs >>= wrapping cClzNaive,
        bcompare matchLabel . bench cblockLabel . nfIO $ xs >>= wrapping cClzBlock,
        bcompare matchLabel . bench cunrolledLabel . nfIO $ xs >>= wrapping cClzBlockUnrolled
      ]

naiveClz :: ByteString -> Int
naiveClz bs = fromMaybe (BS.length bs * 8) $ do
  ix <- BS.findIndex (/= zeroBits) bs
  pure $ ix * 8 + countLeadingZeros (BS.index bs ix)

-- Avoids having to rewrap C ops tediously each time
wrapping :: (Ptr CUChar -> CSize -> CSize) -> ByteString -> IO Int
wrapping f bs = unsafeUseAsCStringLen bs $ \(ptr, len) ->
  pure . fromIntegral . f (castPtr ptr) . fromIntegral $ len

foreign import ccall unsafe "cbits.h c_clz_naive"
  cClzNaive ::
    Ptr CUChar ->
    CSize ->
    CSize

foreign import ccall unsafe "cbits.h c_clz_block"
  cClzBlock ::
    Ptr CUChar ->
    CSize ->
    CSize

foreign import ccall unsafe "cbits.h c_clz_block_unrolled"
  cClzBlockUnrolled ::
    Ptr CUChar ->
    CSize ->
    CSize
