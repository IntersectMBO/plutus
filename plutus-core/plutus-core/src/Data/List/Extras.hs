{-# LANGUAGE RankNTypes #-}

module Data.List.Extras (wix) where

import Control.Lens
import Data.Word

-- | A variant of 'ix' that takes a 'Word64' instead of an 'Int'.
wix :: Word64 -> Traversal' [a] a
wix k f xs0 = go xs0 k
  where
    go [] _ = pure []
    go (a : as) 0 = f a <&> (: as)
    go (a : as) i = (a :) <$> (go as $! i - 1)
