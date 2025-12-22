module PlutusBenchmark.MemoryAnalysis.Types
  ( MeasurementActual (..)
  , MeasurementRaw (..)
  ) where

import PlutusCore.Data qualified as PLC (Data)
import PlutusCore.Value (Value)

-- | Raw measurement record captured directly from generators (before actual measurements)
data MeasurementRaw = MeasurementRaw
  { mrNumPolicies :: Int
  , mrTokensPerPolicy :: Int
  , mrValueMem :: Integer -- ExMemoryUsage-based Value memory
  , mrDataMem :: Integer -- ExMemoryUsage-based Data memory
  , mrTotalSize :: Int
  , mrRatio :: Double
  , mrOuterSize :: Int
  , mrValue :: Value
  , mrData :: PLC.Data -- Output of valueData (Value → Data)
  , mrValueNodeCount :: Int -- Node count for Value
  , mrDataNodeCount :: Int -- Node count for Data
  }

-- | Measurement record for values produced after the first pass
data MeasurementActual = MeasurementActual
  { maNumPolicies :: Int
  , maTokensPerPolicy :: Int
  , maValueMem :: Integer
  , maDataMem :: Integer
  , maTotalSize :: Integer
  , maRatio :: Double
  , maOuterSize :: Int
  , maActualValueMem :: Integer
  , maData :: PLC.Data
  , maValueNodeCount :: Int -- Node count for Value (1 + policies + tokens)
  , maDataNodeCount :: Int -- Node count for Data (all nodes including B/I)
  , maActualDataMem :: Integer -- Actual Data heap (measureGraphWords on mrData)
  }
