-- |
-- Module      : Foundation.Foreign.MemoryMap.Types
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
module Foundation.Foreign.MemoryMap.Types
    ( FileMapping(..)
    , fileMappingToFinalPtr
    , FileMapReadF
    ) where

import GHC.Ptr
import Basement.FinalPtr
import Basement.Types.OffsetSize
import Basement.Compat.Base
import Foundation.VFS (FilePath)

-- | Contains all the information related to a file mapping,
-- including the size and the finalizer function.
data FileMapping = FileMapping
    { fileMappingPtr   :: Ptr Word8
    , fileMappingSize  :: FileSize
    , fileMappingUnmap :: IO ()
    }

-- | From a file mapping, create a final ptr which will automatically
-- unmap memory when the pointer is garbage.
fileMappingToFinalPtr :: FileMapping -> IO (FinalPtr Word8)
fileMappingToFinalPtr (FileMapping ptr _ finalizer) =
    toFinalPtr ptr (const finalizer)

type FileMapReadF = FilePath -> IO FileMapping
