module PlutusCore.Default.Universe.Cardano where

import PlutusCore.Evaluation.Machine.ExMemoryUsage
import PlutusCore.Pretty

import Data.Bits (shiftL)
import Data.ByteString (ByteString)

minBoundInteger, maxBoundInteger :: Integer
minBoundInteger = negate (shiftL 1 262143)
maxBoundInteger = shiftL 1 262143 - 1
{-# NOINLINE minBoundInteger #-}
{-# NOINLINE maxBoundInteger #-}

maxBoundByteString :: Int
maxBoundByteString = 65536
{-# INLINE maxBoundByteString #-}

-- | Cardano on-chain integer
newtype CInteger = CInteger Integer
  deriving newtype (ExMemoryUsage, PrettyBy ConstConfig)

-- | Cardano on-chain bytestring
newtype CByteString = CByteString ByteString
  deriving newtype (ExMemoryUsage, PrettyBy ConstConfig)
