{-# LANGUAGE CPP #-}
module Foundation.Foreign.MemoryMap
    ( fileMapRead
    , FileMapping(..)
    , fileMappingToFinalPtr
    ) where

import Foundation.Foreign.MemoryMap.Types
#ifdef mingw32_HOST_OS
import Foundation.Foreign.MemoryMap.Windows
#else
import Foundation.Foreign.MemoryMap.Posix
#endif

{-
fileMap :: Fd -> Int -> IO FileMap
fileMap = undefined
-}
