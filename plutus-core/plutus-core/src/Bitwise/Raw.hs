{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE MagicHash           #-}
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
import GHC.Exts (Proxy#, proxy#)
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
          ptrs <- MultiPtr <$> do
            arr <- newPrimArray 3
            writePrimArray arr 0 dstPtr
            writePrimArray arr 1 . castPtr $ srcPtr
            writePrimArray arr 2 . castPtr $ srcPtr'
            pure arr
          loop step ptrs len
          unsafePackMallocCStringLen (castPtr dstPtr, len)
    step :: forall (a :: Type) .
      (FiniteBits a, Storable a) =>
      Proxy# a ->
      MultiPtr ->
      IO ()
    step _ mp = do
      srcBlock <- readAndStep @a 1 mp
      srcBlock' <- readAndStep @a 2 mp
      writeAndStep 0 (f srcBlock srcBlock') mp

{-# INLINE loop #-}
loop ::
  (forall (a :: Type) .
    (FiniteBits a, Storable a) =>
    Proxy# a ->
    MultiPtr ->
    IO ()) ->
  MultiPtr ->
  Int ->
  IO ()
loop step mp len = do
  let bigStepSize = sizeOf @Word256 undefined
  let smallerStepSize = sizeOf @Word64 undefined
  let (bigSteps, rest) = len `quotRem` bigStepSize
  let (smallerSteps, smallestSteps) = rest `quotRem` smallerStepSize
  runRefIO mp $ do
    replicateM_ bigSteps . liftRefIO $ step (proxy# @Word256)
    replicateM_ smallerSteps . liftRefIO $ step (proxy# @Word64)
    replicateM_ smallestSteps . liftRefIO $ step (proxy# @Word8)
