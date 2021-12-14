-- |
-- Module      : Foundation.String.Builder
-- License     : BSD-style
-- Maintainer  : Foundation
--
-- String Builder
--
module Foundation.String.Builder
    ( module Basement.String.Builder
    , toString
    ) where

import Basement.String.Builder
import Basement.String (String)
import GHC.ST

-- | run the builder and return a `String`
--
-- alias to `runUnsafe`
--
-- This function is not safe, prefer `run`.
--
toString :: Builder -> String
toString builder = runST (runUnsafe builder)
