-- |
-- Module      : Foundation.Hashing
-- License     : BSD-style
-- Maintainer  : Foundation
--
module Foundation.Hashing
    ( Hashable(..)
    , Hasher
    -- * Specific methods
    , FNV1_32
    , FNV1_64
    , FNV1a_32
    , FNV1a_64
    , Sip1_3
    , Sip2_4
    ) where

import Foundation.Hashing.Hashable
import Foundation.Hashing.Hasher
import Foundation.Hashing.FNV
import Foundation.Hashing.SipHash
