{-# LANGUAGE MagicHash #-}
module System.Random.Mersenne.Pure64.Internal
  ( PureMT(..)

  , blockLen
  , blockSize
  , MTBlock(..)
  ) where

import GHC.Exts
import System.Random.Mersenne.Pure64.Base

-- | 'PureMT', a pure mersenne twister pseudo-random number generator
--
data PureMT  = PureMT {-# UNPACK #-} !MTBlock {-# UNPACK #-} !Int MTBlock

instance Show PureMT where
    show _ = show "<PureMT>"

data MTBlock = MTBlock ByteArray#