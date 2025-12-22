module Main (main) where

import PlutusBenchmark.MemoryAnalysis qualified as Analysis

main :: IO ()
main = do
  measurements <- Analysis.generateMeasurements
  -- Validation experiments (document design decisions)
  Analysis.analyzeValueHeapPredictors measurements
  Analysis.analyzeDataHeapPredictors measurements
  Analysis.analyzeStructurePreservation measurements
  -- Production model (coefficients used in ExMemoryUsage.hs)
  Analysis.analyzeCrossConversionModels measurements
