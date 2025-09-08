-- |Encoder Types
module Flat.Encoder.Types(
  Size,
  NumBits,
  Prim,
  S(..)
) where

import Flat.Types
import GHC.Ptr (Ptr (..))

-- |Add the maximum size in bits of the encoding of value a to a NumBits
type Size a = a -> NumBits -> NumBits

-- |Strict encoder state
data S =
       S
         { nextPtr  :: {-# UNPACK #-} !(Ptr Word8)
         , currByte :: {-# UNPACK #-} !Word8
         , usedBits :: {-# UNPACK #-} !NumBits
         } deriving Show

-- |A basic encoder
type Prim = S -> IO S

