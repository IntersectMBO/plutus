{-# LANGUAGE MagicHash #-}
module Foundation.Foreign.Alloc
    ( allocaBytes
    ) where

import qualified Foreign.Marshal.Alloc as A (allocaBytes)
import           Basement.Imports
import           Basement.Types.OffsetSize

allocaBytes :: CountOf Word8 -> (Ptr a -> IO b) -> IO b
allocaBytes (CountOf i) f = A.allocaBytes i f
