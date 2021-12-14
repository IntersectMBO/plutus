-- |
-- Module      : Foundation.Array.Keyed
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : portable
--
{-# LANGUAGE FlexibleInstances #-}
module Foundation.Collection.Keyed
    ( KeyedCollection(..)
    ) where

import           Basement.Compat.Base
import qualified Data.List

-- | Collection of things that can be looked up by Key
class KeyedCollection c where
    type Key c
    type Value c
    lookup :: Key c -> c -> Maybe (Value c)

instance Eq k => KeyedCollection [(k, v)] where
    type Key [(k,v)] = k
    type Value [(k,v)] = v
    lookup = Data.List.lookup
