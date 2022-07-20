{-# LANGUAGE KindSignatures   #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -ddump-simpl -dsuppress-all #-}

module Bitwise.Raw (
  rawBitwiseBinary
  ) where

import Control.Monad (foldM, foldM_)
import Data.Bits (FiniteBits)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafePackMallocCStringLen, unsafeUseAsCStringLen)
import Data.Kind (Type)
import Data.WideWord.Word256 (Word256)
import Data.Word (Word64, Word8)
import Foreign.Marshal.Alloc (mallocBytes)
import Foreign.Ptr (Ptr, castPtr, plusPtr)
import Foreign.Storable (Storable (peek, poke, sizeOf))
import System.IO.Unsafe (unsafeDupablePerformIO)

{-# NOINLINE rawBitwiseBinary #-}
rawBitwiseBinary ::
  (forall (a :: Type) . (FiniteBits a, Storable a) => a -> a -> a) ->
  ByteString ->
  ByteString ->
  Maybe ByteString
rawBitwiseBinary f bs bs'
  | len /= BS.length bs' = Nothing
  | otherwise = Just go
  where
    len :: Int
    len = BS.length bs
    go :: ByteString
    go = unsafeDupablePerformIO $
      unsafeUseAsCStringLen bs $ \(srcPtr, _) ->
        unsafeUseAsCStringLen bs' $ \(srcPtr', _) -> do
          dstPtr :: Ptr Word8 <- mallocBytes len
          bigStepSmallStep f len dstPtr (castPtr srcPtr) (castPtr srcPtr')
          unsafePackMallocCStringLen (castPtr dstPtr, len)

{-# INLINE bigStepSmallStep #-}
bigStepSmallStep ::
  (forall (a :: Type) . (FiniteBits a, Storable a) => a -> a -> a) ->
  Int ->
  Ptr Word8 ->
  Ptr Word8 ->
  Ptr Word8 ->
  IO ()
bigStepSmallStep f len dstPtr srcPtr srcPtr' = do
  let bigStepSize = sizeOf @Word256 undefined
  let (bigSteps, smallSteps) = len `quotRem` bigStepSize
  let bigPtrs = (castPtr dstPtr, castPtr srcPtr, castPtr srcPtr')
  (mDstPtr, mSrcPtr, mSrcPtr') <- foldM (go @Word256 bigStepSize) bigPtrs . replicate bigSteps $ ()
  let smallPtrs = (castPtr mDstPtr, castPtr mSrcPtr, castPtr mSrcPtr')
  foldM_ (go @Word8 1) smallPtrs . replicate smallSteps $ ()
  where
    go :: forall (a :: Type) .
      (FiniteBits a, Storable a) =>
      Int ->
      (Ptr a, Ptr a, Ptr a) ->
      () ->
      IO (Ptr a, Ptr a, Ptr a)
    go stepSize (dst, src, src') _ = do
      srcBlock <- peek src
      srcBlock' <- peek src'
      poke dst (f srcBlock srcBlock')
      pure (plusPtr dst stepSize, plusPtr src stepSize, plusPtr src' stepSize)
