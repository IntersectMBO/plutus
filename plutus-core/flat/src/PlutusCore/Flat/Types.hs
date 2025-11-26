{-# LANGUAGE FlexibleInstances #-}

-- | Common Types
module PlutusCore.Flat.Types
  ( NumBits
  , module Data.Word
  , module Data.Int
  , Natural
  , SBS.ShortByteString
  , T.Text
  ) where

import Data.ByteString.Short.Internal qualified as SBS
import Data.Int
import Data.Text qualified as T
import Data.Word
import Numeric.Natural

-- | Number of bits
type NumBits = Int
