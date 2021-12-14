-- The -fno-warn-unused-imports flag is to avoid the need for a
-- special Setup.hs in order to use __HADDOCK__ to conditionally
-- import Foreign.C.String.CStringLen only for the sake of Haddock.
-- We avoid the special Setup.hs because in GHC 7.6 the prelude no
-- longer exports 'catch', and it's not entirely clear what sort
-- of exceptions from 'removeFile' actually need handling.
{-# LANGUAGE ForeignFunctionInterface #-}
{-# OPTIONS_GHC -Wall -fwarn-tabs -fno-warn-unused-imports #-}
----------------------------------------------------------------
--                                                    2013.05.29
-- |
-- Module      :  System.Posix.Types.Iovec
-- Copyright   :  Copyright (c) 2010--2015 wren gayle romano
-- License     :  BSD
-- Maintainer  :  wren@community.haskell.org
-- Stability   :  experimental
-- Portability :  non-portable (POSIX.1, XPG4.2; hsc2hs, FFI)
--
-- Imports the C @struct iovec@ type and provides conversion between
-- 'CIovec's and strict 'BS.ByteString's.
----------------------------------------------------------------
module System.Posix.Types.Iovec
    (
    -- * The @struct iovec@ type
      CIovec(..)
    , unsafeByteString2CIovec
    , touchByteString
    , unsafeUseAsCIovec
    , useAsCIovec
    ) where

import           Data.Word                (Word8)
import qualified Data.ByteString          as BS
import qualified Data.ByteString.Internal as BSI
import           Foreign.Ptr              (Ptr)
import qualified Foreign.Ptr              as FFI (castPtr, plusPtr)
import qualified Foreign.ForeignPtr       as FFP
import qualified GHC.ForeignPtr           as GHC_FFP
-- #if ???
-- import qualified Foreign.ForeignPtr.Unsafe as FFP (unsafeForeignPtrToPtr)
-- #endif
import           Foreign.C.Types          (CSize)
import           Foreign.Storable         (Storable(..))

-- N.B., we need a Custom cabal build-type in order for this to
-- work.
-- #ifdef __HADDOCK__
import Foreign.C.String (CStringLen)
-- #endif

-- iovec, writev, and readv are in <sys/uio.h>, but we must include
-- <sys/types.h> and <unistd.h> for legacy reasons.
#include <sys/types.h>
#include <sys/uio.h>
#include <unistd.h>

----------------------------------------------------------------

-- | Haskell type representing the C @struct iovec@ type. This is
-- exactly like @'CStringLen'@ except there's actually struct
-- definition on the C side.
data CIovec = CIovec
    { iov_base :: {-# UNPACK #-} !(Ptr Word8) -- char* or void*
    , iov_len  :: {-# UNPACK #-} !CSize       -- size_t
    }

instance Storable CIovec where
    alignment _ = #{alignment struct iovec}

    sizeOf _    = #{size struct iovec}

    peek ptr = do
        base <- #{peek struct iovec, iov_base} ptr
        len  <- #{peek struct iovec, iov_len}  ptr
        return (CIovec base len)

    poke ptr (CIovec base len) = do
        #{poke struct iovec, iov_base} ptr base
        #{poke struct iovec, iov_len}  ptr len


-- | /O(1) construction/ Convert a @ByteString@ into an @CIovec@.
--
-- This function is /unsafe/ in two ways:
--
-- * After calling this function the @CIovec@ shares the underlying
-- byte buffer with the original @ByteString@. Thus, modifying the
-- @CIovec@ either in C or using poke will cause the contents of
-- the @ByteString@ to change, breaking referential transparency.
-- Other @ByteStrings@ created by sharing (such as those produced
-- via 'BS.take' or 'BS.drop') will also reflect these changes.
--
-- * Also, even though the @CIovec@ shares the underlying byte
-- buffer, it does so in a way that will not keep the original
-- @ByteString@ alive with respect to garbage collection. Thus, the
-- byte buffer could be collected out from under the @CIovec@. To
-- prevent this, you must use 'touchByteString' after the last point
-- where the @CIovec@ is needed.
unsafeByteString2CIovec :: BS.ByteString -> CIovec
unsafeByteString2CIovec (BSI.PS fptr offset len) =
    CIovec
        (GHC_FFP.unsafeForeignPtrToPtr fptr `FFI.plusPtr` offset)
        (fromIntegral len)
{-# INLINE unsafeByteString2CIovec #-}


-- | Keep the @ByteString@ alive. See 'unsafeByteString2CIovec'.
touchByteString :: BS.ByteString -> IO ()
touchByteString (BSI.PS fptr _ _) = FFP.touchForeignPtr fptr
{-# INLINE touchByteString #-}


-- | /O(1) construction/ Use a @ByteString@ with a function requiring
-- a @CIovec@.
--
-- This function does zero copying, and merely unwraps a @ByteString@
-- to appear as an @CIovec@. It is /unsafe/ in the same way as
-- 'unsafeByteString2CIovec'.
unsafeUseAsCIovec :: BS.ByteString -> (CIovec -> IO a) -> IO a
unsafeUseAsCIovec (BSI.PS fptr offset len) io =
    FFP.withForeignPtr fptr $ \ptr ->
        io (CIovec (ptr `FFI.plusPtr` offset) (fromIntegral len))
{-# INLINE unsafeUseAsCIovec #-}
-- The above version saves a case match on @s@ vs using
-- 'unsafeByteString2CIovec' and 'touchByteString'


-- | /O(n) construction/ Use a @ByteString@ with a function requiring
-- a @CIovec@.
--
-- As with 'BS.useAsCString' and 'BS.useAsCStringLen', this function
-- makes a copy of the original @ByteString@ via @memcpy(3)@. The
-- copy will be freed automatically. See 'unsafeUseAsCIovec' for a
-- zero-copying version.
useAsCIovec :: BS.ByteString -> (CIovec -> IO a) -> IO a
useAsCIovec s@(BSI.PS _ _ len) io =
    BS.useAsCString s $ \cstr ->
        io (CIovec (FFI.castPtr cstr) (fromIntegral len))
{-# INLINE useAsCIovec #-}
{-
This definition is essentially verbatim 'BS.useAsCStringLen'. We
can save two 'FFI.castPtr' and one 'fromIntegral' if we instead do
an essentially verbatim 'BS.useAsCString':

    useAsCIovec s@(BSI.PS fptr offset len) io = do
        let lenCSize = fromIntegral len
        FMA.allocaBytes (len+1) $ \buf ->
            FFP.withForeignPtr fptr $ \ptr -> do
                BSI.memcpy buf (ptr `FFI.plusPtr` offset) lenCSize
                pokeByteOff buf len (0 :: Word8) -- add null-terminator
                io (CIovec buf lenCSize)
-}

----------------------------------------------------------------
----------------------------------------------------------- fin.
