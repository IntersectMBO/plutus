{-| Memory analysis for Value/Data conversions.
This module has been refactored into submodules for better organization. -}
module PlutusBenchmark.MemoryAnalysis
  ( -- * Experiments
    generateMeasurements
  , analyzeValueHeapPredictors
  , analyzeDataHeapPredictors
  , analyzeStructurePreservation
  , analyzeCrossConversionModels

    -- * Types
  , MeasurementActual (..)

    -- * Generators
  , generateUniformValue
  , generateWorstCaseValue

    -- * Utilities
  , countNodes
  , countValueNodes
  ) where

import PlutusBenchmark.MemoryAnalysis.Experiments
import PlutusBenchmark.MemoryAnalysis.Generators (generateUniformValue, generateWorstCaseValue)
import PlutusBenchmark.MemoryAnalysis.Helpers (countNodes, countValueNodes)
import PlutusBenchmark.MemoryAnalysis.Types (MeasurementActual (..))
