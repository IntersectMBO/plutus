{-# LANGUAGE CPP, ForeignFunctionInterface, MagicHash, UnliftedFFITypes #-}

-- |
-- Module      : Data.Double.Conversion.FFI
-- Copyright   : (c) 2011 MailRank, Inc.
--
-- License     : BSD-style
-- Maintainer  : bos@serpentine.com
-- Stability   : experimental
-- Portability : GHC
--
-- FFI interface support for converting between double precision
-- floating point values and text.

module Data.Double.Conversion.FFI
    (
      c_Text_ToExponential
    , c_Text_ToFixed
    , c_Text_ToPrecision
    , c_Text_ToShortest
    , c_ToExponentialLength
    , c_ToFixedLength
    , c_ToPrecisionLength
    , c_ToShortestLength
    , c_ToExponential
    , c_ToFixed
    , c_ToPrecision
    , c_ToShortest
    ) where

import Data.Word (Word8)
#if __GLASGOW_HASKELL__ >= 703
import Foreign.C.Types (CDouble(CDouble), CInt(CInt))
#else
import Foreign.C.Types (CDouble, CInt)
#endif
import Foreign.Ptr (Ptr)
import GHC.Prim (MutableByteArray#)

foreign import ccall unsafe "hs-double-conversion.h _hs_ToShortestLength"
    c_ToShortestLength :: CInt

foreign import ccall unsafe "hs-double-conversion.h _hs_Text_ToShortest"
    c_Text_ToShortest :: CDouble -> MutableByteArray# s -> IO CInt

foreign import ccall unsafe "hs-double-conversion.h _hs_ToShortest"
    c_ToShortest :: CDouble -> Ptr Word8 -> IO CInt

foreign import ccall unsafe "hs-double-conversion.h _hs_ToFixedLength"
    c_ToFixedLength :: CInt

foreign import ccall unsafe "hs-double-conversion.h _hs_Text_ToFixed"
    c_Text_ToFixed :: CDouble -> MutableByteArray# s -> CInt -> IO CInt

foreign import ccall unsafe "hs-double-conversion.h _hs_ToFixed"
    c_ToFixed :: CDouble -> Ptr Word8 -> CInt -> IO CInt

foreign import ccall unsafe "hs-double-conversion.h _hs_ToExponentialLength"
    c_ToExponentialLength :: CInt

foreign import ccall unsafe "hs-double-conversion.h _hs_Text_ToExponential"
    c_Text_ToExponential :: CDouble -> MutableByteArray# s -> CInt -> IO CInt

foreign import ccall unsafe "hs-double-conversion.h _hs_ToExponential"
    c_ToExponential :: CDouble -> Ptr Word8 -> CInt -> IO CInt

foreign import ccall unsafe "hs-double-conversion.h _hs_ToPrecisionLength"
    c_ToPrecisionLength :: CInt

foreign import ccall unsafe "hs-double-conversion.h _hs_Text_ToPrecision"
    c_Text_ToPrecision :: CDouble -> MutableByteArray# s -> CInt -> IO CInt

foreign import ccall unsafe "hs-double-conversion.h _hs_ToPrecision"
    c_ToPrecision :: CDouble -> Ptr Word8 -> CInt -> IO CInt
