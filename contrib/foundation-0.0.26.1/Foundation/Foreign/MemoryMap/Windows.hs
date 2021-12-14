module Foundation.Foreign.MemoryMap.Windows
    ( fileMapRead
    ) where

import System.Win32.Mem
import System.Win32.File
import System.Win32.FileMapping
import Control.Exception hiding (handle)

import Basement.Compat.Base
import Basement.Types.OffsetSize
import Foundation.VFS
import Foundation.Foreign.MemoryMap.Types

fileMapRead :: FileMapReadF
fileMapRead path = bracket doOpen closeHandle doMapping
  where
    doOpen           = createFile (filePathToLString path) gENERIC_READ fILE_SHARE_READ Nothing oPEN_EXISTING fILE_ATTRIBUTE_NORMAL Nothing
    doMapping handle = bracket (createFileMapping (Just handle) pAGE_READONLY 0 Nothing)
                               closeHandle
                               (getSizeAndMap handle)
    getSizeAndMap handle filemap = do
        fileInfo <- getFileInformationByHandle handle
        mask_ $ do
            ptr <- mapViewOfFile filemap fILE_MAP_READ 0 0
            return $ FileMapping ptr (FileSize $ bhfiSize fileInfo) (unmapViewOfFile ptr)
