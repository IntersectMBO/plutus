module PlutusBenchmark.MemoryAnalysis.Helpers
  ( memU
  , measureGraphWords
  , countNodes
  , countValueNodes
  , printSectionHeader
  , computeSSE
  , computeR2
  ) where

import Prelude

import Control.DeepSeq (NFData, force)
import Control.Exception (evaluate)
import Data.Map.Strict qualified as Map
import Data.SatInt (fromSatInt)
import GHC.DataSize qualified as DS
import PlutusCore.Data qualified as PLC (Data (..))
import PlutusCore.Evaluation.Machine.CostStream (sumCostStream)
import PlutusCore.Evaluation.Machine.ExMemoryUsage (ExMemoryUsage (..), flattenCostRose)
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as Value

--------------------------------------------------------------------------------
-- Memory Measurement ----------------------------------------------------------

-- | Memory usage calculation via ExMemoryUsage
memU :: ExMemoryUsage a => a -> Integer
memU x = fromSatInt (sumCostStream (flattenCostRose (memoryUsage x)))

-- | Measure size by walking the object graph in 64-bit words; resistant to heap churn
measureGraphWords :: NFData a => a -> IO Integer
measureGraphWords x = do
  x' <- evaluate (force x)
  sz <- DS.recursiveSize x'
  pure (fromIntegral sz `div` 8)

--------------------------------------------------------------------------------
-- Node Counting ---------------------------------------------------------------

-- | Count nodes in a Data structure (all constructors including B and I leaves)
countNodes :: PLC.Data -> Int
countNodes (PLC.Constr _ ds) = 1 + sum (map countNodes ds)
countNodes (PLC.Map pairs) = 1 + sum (map (\(k, v) -> countNodes k + countNodes v) pairs)
countNodes (PLC.List ds) = 1 + sum (map countNodes ds)
countNodes (PLC.I _) = 1
countNodes (PLC.B _) = 1

{-| Count nodes in a Value structure by traversing nested maps.
Counts: 1 (root) + 1 per policy (outer map entry) + 1 per token (inner map entry)
This matches the CostRose traversal pattern used in ExMemoryUsage. -}
countValueNodes :: Value -> Int
countValueNodes v =
  let nested = Value.unpack v
   in 1 + sum [1 + Map.size inner | inner <- Map.elems nested]

--------------------------------------------------------------------------------
-- Regression Statistics -------------------------------------------------------

-- | Compute sum of squared errors
computeSSE :: Integer -> Integer -> [(Integer, Integer)] -> Double
computeSSE slope intercept pts =
  sum
    [ (fromIntegral y - (fromIntegral slope * fromIntegral x + fromIntegral intercept)) ** 2
    | (x, y) <- pts
    ]

-- | Compute R-squared statistic
computeR2 :: Double -> [(Integer, Integer)] -> Double
computeR2 sse pts =
  let meanY = fromIntegral (sum (map snd pts)) / fromIntegral (length pts)
      ssTot = sum [(fromIntegral y - meanY) ** 2 | (_, y) <- pts]
   in 1 - sse / ssTot

--------------------------------------------------------------------------------
-- Output Formatting -----------------------------------------------------------

-- | Print a standardized section header used by the main analysis flow
printSectionHeader :: String -> IO ()
printSectionHeader title = do
  putStrLn ""
  putStrLn "=========================================="
  putStrLn title
  putStrLn "=========================================="
  putStrLn ""
