-- |
-- Module      : Foundation.IO
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
-- IO Routine
module Foundation.IO
    (
    -- * Terminal
      Foundation.IO.Terminal.putStrLn
    , Foundation.IO.Terminal.putStr
    , Foundation.IO.Terminal.stdin
    , Foundation.IO.Terminal.stdout
    -- * File
    , Foundation.IO.File.IOMode(..)
    , Foundation.IO.File.openFile
    , Foundation.IO.File.closeFile
    , Foundation.IO.File.withFile
    , Foundation.IO.File.hGet
    , Foundation.IO.File.hPut
    , Foundation.IO.File.readFile
    ) where

import qualified Foundation.IO.Terminal
import qualified Foundation.IO.File
