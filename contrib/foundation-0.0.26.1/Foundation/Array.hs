-- |
-- Module      : Foundation.Array
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
-- Simple Array and Almost-Array-like data structure
--
-- Generally accessible in o(1)
--
{-# LANGUAGE MagicHash #-}
module Foundation.Array
    ( Array
    , MArray
    , UArray
    , MUArray
    , ChunkedUArray
    , Bitmap
    , MutableBitmap
    , PrimType
    -- exceptions
    , OutOfBound
    ) where

import           Basement.Exception
import           Basement.BoxedArray
import           Basement.UArray
import           Basement.UArray.Mutable
import           Foundation.Array.Bitmap
import           Foundation.Array.Chunked.Unboxed
