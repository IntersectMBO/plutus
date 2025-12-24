{-# LANGUAGE BlockArguments #-}

module PlutusBenchmark.MemoryAnalysis.Experiments
  ( generateMeasurements
  , analyzeValueHeapPredictors
  , analyzeDataHeapPredictors
  , analyzeStructurePreservation
  , analyzeCrossConversionModels
  ) where

import Prelude

import Data.Function ((&))
import Data.Functor ((<&>))
import PlutusBenchmark.MemoryAnalysis.Generators (generateUniformValue, generateWorstCaseValue)
import PlutusBenchmark.MemoryAnalysis.Helpers
  ( computeR2
  , computeSSE
  , countNodes
  , countValueNodes
  , measureGraphWords
  , memU
  , printSectionHeader
  )
import PlutusBenchmark.MemoryAnalysis.Types (MeasurementActual (..), MeasurementRaw (..))
import PlutusBenchmark.Plotting (savePredictionPlot)
import PlutusBenchmark.RegressionInteger (integerBestFit)
import PlutusCore.Value qualified as Value
import Text.Printf (printf)

--------------------------------------------------------------------------------
-- Measurement Generation ------------------------------------------------------

{-| Generate measurements for all experiments.
This is the shared data collection pass used by all analysis functions. -}
generateMeasurements :: IO [MeasurementActual]
generateMeasurements = do
  printSectionHeader "Memory Analysis Experiments"

  let testSizes = [1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128]

  putStrLn "Generating test Values and measuring memory usage..."
  putStrLn ""

  -- Collect raw measurements using uniform distribution
  let measurementsRaw =
        [ (numPolicies, tokensPerPolicy)
        | numPolicies <- testSizes
        , tokensPerPolicy <- testSizes
        ]
          <&> \(numPolicies, tokensPerPolicy) ->
            let value = generateUniformValue numPolicies tokensPerPolicy
                data' = Value.valueData value
                valueMem = memU value
                dataMem = memU data'
             in MeasurementRaw
                  { mrNumPolicies = numPolicies
                  , mrTokensPerPolicy = tokensPerPolicy
                  , mrValueMem = valueMem
                  , mrDataMem = dataMem
                  , mrTotalSize = Value.totalSize value
                  , mrRatio =
                      if valueMem > 0
                        then fromIntegral dataMem / fromIntegral valueMem
                        else 0
                  , mrOuterSize = numPolicies
                  , mrValue = value
                  , mrData = data'
                  , mrValueNodeCount = countValueNodes value
                  , mrDataNodeCount = countNodes data'
                  }

  -- Second pass: measure actual graph sizes
  measurementsRaw & mapM \mr -> do
    actualValueMem <- measureGraphWords (mrValue mr)
    actualDataMem <- measureGraphWords (mrData mr)

    pure
      MeasurementActual
        { maNumPolicies = mrNumPolicies mr
        , maTokensPerPolicy = mrTokensPerPolicy mr
        , maValueMem = mrValueMem mr
        , maDataMem = mrDataMem mr
        , maTotalSize = toInteger (mrTotalSize mr)
        , maRatio = mrRatio mr
        , maOuterSize = mrOuterSize mr
        , maActualValueMem = actualValueMem
        , maData = mrData mr
        , maValueNodeCount = mrValueNodeCount mr
        , maDataNodeCount = mrDataNodeCount mr
        , maActualDataMem = actualDataMem
        }

--------------------------------------------------------------------------------
-- Value Heap Predictors -------------------------------------------------------

{-| Compare totalSize vs nodeCount as predictors for Value heap memory.
FUTURE REFERENCE: Shows nodeCount achieves higher R² for real-case structure.
Currently using totalSize for simplicity; keep this for potential future switch. -}
analyzeValueHeapPredictors :: [MeasurementActual] -> IO ()
analyzeValueHeapPredictors measurements = do
  printSectionHeader "Value Heap Memory: totalSize vs nodeCount"

  -- Data points: (predictor, actualValueHeap)
  let totalSizePoints = [(maTotalSize m, maActualValueMem m) | m <- measurements]
      nodeCountPoints = [(toInteger (maValueNodeCount m), maActualValueMem m) | m <- measurements]

  -- Fit linear models
  let (totalSizeSlope, totalSizeIntercept) = integerBestFit totalSizePoints
      (nodeCountSlope, nodeCountIntercept) = integerBestFit nodeCountPoints

  -- Compute SSE and R² for each model
  let totalSizeSSE = computeSSE totalSizeSlope totalSizeIntercept totalSizePoints
      nodeCountSSE = computeSSE nodeCountSlope nodeCountIntercept nodeCountPoints
      totalSizeR2 = computeR2 totalSizeSSE totalSizePoints
      nodeCountR2 = computeR2 nodeCountSSE nodeCountPoints

  putStrLn "Model 1: ValueHeap = slope * totalSize + intercept"
  printf "  Coefficients: slope=%d, intercept=%d\n" totalSizeSlope totalSizeIntercept
  printf "  SSE: %.2f\n" totalSizeSSE
  printf "  R²: %.6f\n" totalSizeR2
  putStrLn ""

  putStrLn "Model 2: ValueHeap = slope * nodeCount + intercept"
  printf "  Coefficients: slope=%d, intercept=%d\n" nodeCountSlope nodeCountIntercept
  printf "  SSE: %.2f\n" nodeCountSSE
  printf "  R²: %.6f\n" nodeCountR2
  putStrLn ""

  let winner = if nodeCountR2 > totalSizeR2 then "nodeCount" else "totalSize"
  printf "Better predictor: %s (higher R²)\n" winner

  -- Generate comparison plots
  savePredictionPlot
    "value_heap_totalsize_predictor.svg"
    (printf "Value Heap vs totalSize (R²=%.4f)" totalSizeR2)
    "totalSize"
    "Value Heap Memory (words)"
    totalSizePoints
    (totalSizeSlope, totalSizeIntercept)

  savePredictionPlot
    "value_heap_nodecount_predictor.svg"
    (printf "Value Heap vs nodeCount (R²=%.4f)" nodeCountR2)
    "nodeCount"
    "Value Heap Memory (words)"
    nodeCountPoints
    (nodeCountSlope, nodeCountIntercept)

  putStrLn "Plot saved as 'plutus-benchmark/memory-analysis/data/value_heap_totalsize_predictor.svg'"
  putStrLn "Plot saved as 'plutus-benchmark/memory-analysis/data/value_heap_nodecount_predictor.svg'"

--------------------------------------------------------------------------------
-- Data Heap Predictors --------------------------------------------------------

{-| Compare totalSize vs nodeCount as predictors for Data heap memory.
FUTURE REFERENCE: Shows nodeCount achieves higher R² for real-case structure.
Currently using totalSize for ValueData; keep this for potential future switch. -}
analyzeDataHeapPredictors :: [MeasurementActual] -> IO ()
analyzeDataHeapPredictors measurements = do
  printSectionHeader "Data Heap Memory: totalSize vs nodeCount"

  -- Data points: (predictor, actualDataHeap)
  let totalSizePoints = [(maTotalSize m, maActualDataMem m) | m <- measurements]
      nodeCountPoints = [(toInteger (maDataNodeCount m), maActualDataMem m) | m <- measurements]

  -- Fit linear models
  let (totalSizeSlope, totalSizeIntercept) = integerBestFit totalSizePoints
      (nodeCountSlope, nodeCountIntercept) = integerBestFit nodeCountPoints

  -- Compute SSE and R² for each model
  let totalSizeSSE = computeSSE totalSizeSlope totalSizeIntercept totalSizePoints
      nodeCountSSE = computeSSE nodeCountSlope nodeCountIntercept nodeCountPoints
      totalSizeR2 = computeR2 totalSizeSSE totalSizePoints
      nodeCountR2 = computeR2 nodeCountSSE nodeCountPoints

  putStrLn "Model 1: DataHeap = slope * totalSize + intercept"
  printf "  Coefficients: slope=%d, intercept=%d\n" totalSizeSlope totalSizeIntercept
  printf "  SSE: %.2f\n" totalSizeSSE
  printf "  R²: %.6f\n" totalSizeR2
  putStrLn ""

  putStrLn "Model 2: DataHeap = slope * nodeCount + intercept"
  printf "  Coefficients: slope=%d, intercept=%d\n" nodeCountSlope nodeCountIntercept
  printf "  SSE: %.2f\n" nodeCountSSE
  printf "  R²: %.6f\n" nodeCountR2
  putStrLn ""

  let winner = if nodeCountR2 > totalSizeR2 then "nodeCount" else "totalSize"
  printf "Better predictor: %s (higher R²)\n" winner

  -- Generate comparison plots
  savePredictionPlot
    "data_heap_totalsize_predictor.svg"
    (printf "Data Heap vs totalSize (R²=%.4f)" totalSizeR2)
    "totalSize"
    "Data Heap Memory (words)"
    totalSizePoints
    (totalSizeSlope, totalSizeIntercept)

  savePredictionPlot
    "data_heap_nodecount_predictor.svg"
    (printf "Data Heap vs nodeCount (R²=%.4f)" nodeCountR2)
    "nodeCount"
    "Data Heap Memory (words)"
    nodeCountPoints
    (nodeCountSlope, nodeCountIntercept)

  putStrLn "Plot saved as 'plutus-benchmark/memory-analysis/data/data_heap_totalsize_predictor.svg'"
  putStrLn "Plot saved as 'plutus-benchmark/memory-analysis/data/data_heap_nodecount_predictor.svg'"

--------------------------------------------------------------------------------
-- Structure Preservation ------------------------------------------------------

{-| Compare worst-case (flattened) vs real-case (structure-preserving).
DOCUMENTATION: Validates the worst-case assumption used in ValueData costing.
Shows that totalSize gives perfect R²=1.0 when structure is flattened. -}
analyzeStructurePreservation :: [MeasurementActual] -> IO ()
analyzeStructurePreservation measurements = do
  printSectionHeader "Structure Preservation Comparison"

  putStrLn "Real-case (uniform): Each policy gets tokensPerPolicy tokens"
  putStrLn "Worst-case (flattened): Each policy gets exactly 1 token"
  putStrLn ""

  -- Generate worst-case measurements with flattened structure
  let testSizes = [1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128]

  putStrLn "Generating worst-case Values and measuring..."
  worstCaseMeasurements <-
    testSizes & mapM \totalSize -> do
      let value = generateWorstCaseValue totalSize
          data' = Value.valueData value
      actualValueMem <- measureGraphWords value
      actualDataMem <- measureGraphWords data'

      pure (totalSize, actualValueMem, actualDataMem, countValueNodes value, countNodes data')

  -- Compare totalSize predictor for both approaches
  let realCasePoints = [(maTotalSize m, maActualValueMem m) | m <- measurements]
      worstCasePoints = [(toInteger ts, vm) | (ts, vm, _, _, _) <- worstCaseMeasurements]

  -- Fit models
  let (realSlope, realIntercept) = integerBestFit realCasePoints
      (worstSlope, worstIntercept) = integerBestFit worstCasePoints

  -- Compute SSE and R²
  let realSSE = computeSSE realSlope realIntercept realCasePoints
      worstSSE = computeSSE worstSlope worstIntercept worstCasePoints
      realR2 = computeR2 realSSE realCasePoints
      worstR2 = computeR2 worstSSE worstCasePoints

  putStrLn "Real-case (uniform): ValueHeap = slope * totalSize + intercept"
  printf "  Coefficients: slope=%d, intercept=%d\n" realSlope realIntercept
  printf "  SSE: %.2f, R²: %.6f\n" realSSE realR2
  putStrLn ""

  putStrLn "Worst-case (flattened): ValueHeap = slope * totalSize + intercept"
  printf "  Coefficients: slope=%d, intercept=%d\n" worstSlope worstIntercept
  printf "  SSE: %.2f, R²: %.6f\n" worstSSE worstR2
  putStrLn ""

  printf "Worst-case R² should be ≈1.0 (structure is deterministic given totalSize)\n"

  -- Generate comparison plot
  savePredictionPlot
    "value_heap_worstcase.svg"
    (printf "Value Heap (Worst-case) vs totalSize (R²=%.4f)" worstR2)
    "totalSize"
    "Value Heap Memory (words)"
    worstCasePoints
    (worstSlope, worstIntercept)

  putStrLn "Plot saved as 'plutus-benchmark/memory-analysis/data/value_heap_worstcase.svg'"

--------------------------------------------------------------------------------
-- Cross-Conversion Models -----------------------------------------------------

{-| PRODUCTION MODEL: Derive cross-conversion coefficients for ExMemoryUsage.

ValueData builtin (Value → Data):
  Uses totalSize with worst-case (flattened) structure assumption
  Perfect fit (R²=1.0), slightly pessimistic
  Used by: ValueTotalSizeToDataHeap wrapper in ExMemoryUsage.hs

UnValueData builtin (Data → Value):
  Counts INPUT Data nodes → predicts OUTPUT Value heap
  Model: ValueHeap = 6 * dataNodeCount + 27 (R²=0.973)
  Used by: DataNodeCountToValueHeap wrapper in ExMemoryUsage.hs

See plutus-core/plutus-core/src/PlutusCore/Evaluation/Machine/ExMemoryUsage.hs -}
analyzeCrossConversionModels :: [MeasurementActual] -> IO ()
analyzeCrossConversionModels measurements = do
  printSectionHeader "Cross-Conversion Models (PRODUCTION)"

  putStrLn "ValueData: Input Value → Output Data"
  putStrLn "UnValueData: Input Data → Output Value"
  putStrLn ""

  -- Generate worst-case measurements for ValueData model
  let testSizes = [1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 32, 40, 48, 64, 80, 96, 128]

  putStrLn "Generating worst-case Values for ValueData model..."
  worstCaseMeasurements <-
    testSizes & mapM \totalSize -> do
      let value = generateWorstCaseValue totalSize
          data' = Value.valueData value
      actualDataMem <- measureGraphWords data'

      pure (totalSize, actualDataMem)

  -- ValueData: Input Value totalSize → Output Data actual heap (worst-case)
  let valueDataPoints = [(toInteger ts, dm) | (ts, dm) <- worstCaseMeasurements]
      (vdSlope, vdIntercept) = integerBestFit valueDataPoints
      vdSSE = computeSSE vdSlope vdIntercept valueDataPoints
      vdR2 = computeR2 vdSSE valueDataPoints

  putStrLn "ValueData: OutputDataHeap = slope * inputTotalSize + intercept (worst-case)"
  printf "  Coefficients: slope=%d, intercept=%d\n" vdSlope vdIntercept
  printf "  SSE: %.2f, R²: %.6f\n" vdSSE vdR2
  putStrLn ""

  -- UnValueData: Input Data nodeCount → Output Value actual heap
  let unValueDataPoints = [(toInteger (maDataNodeCount m), maActualValueMem m) | m <- measurements]
      (uvdSlope, uvdIntercept) = integerBestFit unValueDataPoints
      uvdSSE = computeSSE uvdSlope uvdIntercept unValueDataPoints
      uvdR2 = computeR2 uvdSSE unValueDataPoints

  putStrLn "UnValueData: OutputValueHeap = slope * inputDataNodeCount + intercept"
  printf "  Coefficients: slope=%d, intercept=%d\n" uvdSlope uvdIntercept
  printf "  SSE: %.2f, R²: %.6f\n" uvdSSE uvdR2
  putStrLn ""

  putStrLn "These are the PRODUCTION models for the ExMemoryUsage wrappers:"
  printf
    "  ValueTotalSizeToDataHeap: %d * totalSize + %d (predicts output Data heap, R²=%.3f)\n"
    vdSlope
    vdIntercept
    vdR2
  printf
    "  DataNodeCountToValueHeap: %d * dataNodeCount + %d (predicts output Value heap, R²=%.3f)\n"
    uvdSlope
    uvdIntercept
    uvdR2

  -- Generate plots
  savePredictionPlot
    "valuedata_production_model.svg"
    (printf "ValueData Model: OutputDataHeap = %d*totalSize + %d (R²=%.4f)" vdSlope vdIntercept vdR2)
    "Input Value totalSize"
    "Output Data Heap (words)"
    valueDataPoints
    (vdSlope, vdIntercept)

  savePredictionPlot
    "unvaluedata_production_model.svg"
    (printf "UnValueData Model: OutputValueHeap = %d*dataNodeCount + %d (R²=%.4f)" uvdSlope uvdIntercept uvdR2)
    "Input Data nodeCount"
    "Output Value Heap (words)"
    unValueDataPoints
    (uvdSlope, uvdIntercept)

  putStrLn "Plot saved as 'plutus-benchmark/memory-analysis/data/valuedata_production_model.svg'"
  putStrLn "Plot saved as 'plutus-benchmark/memory-analysis/data/unvaluedata_production_model.svg'"
