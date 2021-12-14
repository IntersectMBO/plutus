-- |
-- Module      : Foundation.VFS
-- License     : BSD-style
-- Maintainer  : foundation
-- Stability   : experimental
-- Portability : portable
--
module Foundation.VFS
    ( Path(..)
    , filename
    , parent
    , prefix
    , suffix

      -- * FilePath
    , FilePath
    , FileName
      -- ** conversion
    , filePathToString
    , filePathToLString
    ) where


import Foundation.VFS.Path
          ( Path(..)
          , filename, parent, suffix, prefix
          )
import Foundation.VFS.FilePath
          ( FilePath, FileName
          , filePathToString
          , filePathToLString
          )
