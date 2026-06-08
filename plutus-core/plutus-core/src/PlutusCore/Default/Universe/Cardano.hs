module PlutusCore.Default.Universe.Cardano where

import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Pretty

import Data.Bits (shiftL)
import Data.ByteString (ByteString)

maxBoundByteString :: Int
maxBoundByteString = 65536
{-# INLINE maxBoundByteString #-}

-- | Cardano on-chain bytestring
newtype CByteString = CByteString ByteString
  deriving newtype (ExMemoryUsage, PrettyBy ConstConfig)
