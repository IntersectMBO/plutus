-- |
-- Module      : Foundation.Array.Internal
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
-- Give access to Array non public functions which
-- can be used to make certains optimisations.
--
-- Most of what is available here has no guarantees of stability.
-- Anything can be removed and changed.
--
module Foundation.Array.Internal
    ( UArray(..)
    , fromForeignPtr
    , withPtr
    , copyToPtr
    , recast
    , toHexadecimal
    -- * Mutable facilities
    , new
    , newPinned
    , withMutablePtr
    ) where

import           Basement.UArray
import           Basement.UArray.Mutable hiding (copyToPtr)
