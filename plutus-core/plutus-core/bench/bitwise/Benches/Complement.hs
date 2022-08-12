-- editorconfig-checker-disable-file
module Benches.Complement (
  benches
  ) where

import Data.Bits (complement)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Internal (fromForeignPtr, mallocByteString)
import Data.ByteString.Unsafe (unsafeUseAsCStringLen)
import DataGen (mkUnaryArg, noCleanup, sizes)
import Foreign.C.Types (CSize (CSize), CUChar)
import Foreign.ForeignPtr (castForeignPtr, withForeignPtr)
import Foreign.Ptr (Ptr, castPtr)
import Test.Tasty (withResource)
import Test.Tasty.Bench (Benchmark, bcompare, bench, bgroup, nfIO)

benches :: Benchmark
benches = bgroup "Basic complement" $ benchBasic "Basic complement" <$> sizes

-- Helpers

-- Benchmark a naive Haskell implementation against the C one
benchBasic ::
  String ->
  Int ->
  Benchmark
benchBasic mainLabel len =
  withResource (mkUnaryArg len) noCleanup $ \xs ->
    let naiveLabel = "map"
        cnaiveLabel = "naive C"
        testLabel = mainLabel <> ", length " <> show len
        matchLabel = "$NF == \"" <> naiveLabel <> "\" && $(NF - 1) == \"" <> testLabel <> "\"" in
      bgroup testLabel [
        bench naiveLabel . nfIO $ BS.map complement <$> xs,
        bcompare matchLabel . bench cnaiveLabel . nfIO $ xs >>= wrapping cComplementNaive
        ]

-- Avoids having to rewrap C complement ops tediously each time
wrapping :: (Ptr CUChar -> Ptr CUChar -> CSize -> IO ()) -> ByteString -> IO ByteString
wrapping f bs = unsafeUseAsCStringLen bs $ \(ptr, len) -> do
  fp <- mallocByteString len
  withForeignPtr fp $ \dst -> f dst (castPtr ptr) (fromIntegral len)
  pure . fromForeignPtr (castForeignPtr fp) 0 $ len

foreign import ccall unsafe "cbits.h c_complement_naive"
  cComplementNaive ::
    Ptr CUChar ->
    Ptr CUChar ->
    CSize ->
    IO ()
