{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeApplications    #-}

module Bitwise.Raw (
  rawBitwiseBinary
  ) where

import Bitwise.RefIO (MultiPtr (MultiPtr), RefIO, liftRefIO, readAndStep, runRefIO, writeAndStep)
import Control.Monad (replicateM_)
import Data.Bits (FiniteBits)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Unsafe (unsafePackMallocCStringLen, unsafeUseAsCStringLen)
import Data.Kind (Type)
import Data.Primitive.PrimArray (newPrimArray, writePrimArray)
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
  let smallerStepSize = sizeOf @Word64 undefined
  let (bigSteps, rest) = len `quotRem` bigStepSize
  let (smallerSteps, smallSteps) = rest `quotRem` smallerStepSize
  ptrs <- MultiPtr <$> do
    arr <- newPrimArray 3
    writePrimArray arr 0 dstPtr
    writePrimArray arr 1 srcPtr
    writePrimArray arr 2 srcPtr'
    pure arr
  runRefIO ptrs $ do
    replicateM_ bigSteps $ go @Word256
    replicateM_ smallerSteps $ go @Word64
    replicateM_ smallSteps $ go @Word8
  where
    go ::
      forall (a :: Type) .
      (Storable a, FiniteBits a) =>
      RefIO ()
    go = do
      srcBlock <- liftRefIO (readAndStep @a 1)
      srcBlock' <- liftRefIO (readAndStep @a 2)
      liftRefIO (writeAndStep 0 (f srcBlock srcBlock'))
