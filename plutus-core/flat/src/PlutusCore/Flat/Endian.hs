{-# LANGUAGE CPP #-}
-- | Endian utilities
--
-- Exported for testing purposes, but not meant to be used outside this package.
module PlutusCore.Flat.Endian
    (
    toBE32
    , toBE64
    , toBE16
    , isBigEndian
    -- , fix64
    ) where

#include "MachDeps.h"

import Data.Word (Word16, Word32, Word64, byteSwap16, byteSwap32, byteSwap64)

-- #ifdef ghcjs_HOST_OS
-- import Data.Bits
-- #endif

-- $setup
-- >>> import Numeric (showHex)

isBigEndian :: Bool
isBigEndian =
#if defined(WORDS_BIGENDIAN) || defined(ETA_VERSION)
    True
#else
    False
#endif


{- |
Convert a 64 bit value in cpu endianess to big endian

>>> toBE64 0xF0F1F2F3F4F5F6F7 == if isBigEndian then 0xF0F1F2F3F4F5F6F7 else 0xF7F6F5F4F3F2F1F0
True
-}
toBE64 :: Word64 -> Word64
#if defined(WORDS_BIGENDIAN) || defined(ETA_VERSION)
toBE64 = id
#else
toBE64 = byteSwap64
#endif

{- |
Convert a 32 bit value in cpu endianess to big endian

>>> toBE32 0xF0F1F2F3 == if isBigEndian then 0xF0F1F2F3 else 0xF3F2F1F0
True
-}
toBE32 :: Word32 -> Word32
#if defined(WORDS_BIGENDIAN) || defined(ETA_VERSION)
toBE32 = id
#else
toBE32 = byteSwap32
#endif

{- |
Convert a 16 bit value in cpu endianess to big endian

>>> toBE16 0xF0F1 == if isBigEndian then 0xF0F1 else 0xF1F0
True
-}
toBE16 :: Word16 -> Word16
#if defined(WORDS_BIGENDIAN) || defined(ETA_VERSION)
toBE16 = id
#else
toBE16 = byteSwap16
#endif
