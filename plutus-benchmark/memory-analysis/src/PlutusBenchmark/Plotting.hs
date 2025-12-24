module PlutusBenchmark.Plotting
  ( dataOutDir
  , savePredictionPlot
  , saveScatterPlot
  , generateScatterPlot
  , ensureDataDir
  ) where

import Prelude

import Data.Colour.SRGB (sRGB24)
import Graphics.Rendering.Chart.Backend.Diagrams (toFile)
import Graphics.Rendering.Chart.Easy
import System.Directory (createDirectoryIfMissing)

-- Directory where generated plots are written
dataOutDir :: FilePath
dataOutDir = "plutus-benchmark/memory-analysis/data"

ensureDataDir :: IO ()
ensureDataDir = createDirectoryIfMissing True dataOutDir

-- Save a prediction plot: model line (slope/intercept) + actual points
savePredictionPlot
  :: FilePath -- filename (relative, will be placed under dataOutDir)
  -> String -- title
  -> String -- x title
  -> String -- y title
  -> [(Integer, Integer)] -- actual points (x,y)
  -> (Integer, Integer) -- (slope, intercept)
  -> IO ()
savePredictionPlot filename title xTitle yTitle actualPoints (slope, intercept) = do
  ensureDataDir
  let outPath = dataOutDir ++ "/" ++ filename
      actualD =
        map
          ( \(x, y) ->
              ( fromIntegral x :: Double
              , fromIntegral y :: Double
              )
          )
          actualPoints
      predicted =
        [ ( fromIntegral x :: Double
          , fromIntegral slope * fromIntegral x + fromIntegral intercept
          )
        | (x, _) <- actualPoints
        ]
  toFile def outPath $ do
    layout_title .= title
    layout_x_axis . laxis_title .= xTitle
    layout_y_axis . laxis_title .= yTitle
    setColors [opaque (sRGB24 255 0 0), opaque (sRGB24 0 0 255)]
    plot $ line "Predicted (model)" [predicted]
    plot $ points "Actual" actualD

-- Save a scatter plot with fitted model line computed at same x values
saveScatterPlot
  :: FilePath
  -> String
  -> String
  -> String
  -> [(Integer, Integer)]
  -> Integer -- slope
  -> Integer -- intercept
  -> IO ()
saveScatterPlot filename title xTitle yTitle plotData slope intercept = do
  ensureDataDir
  let outPath = dataOutDir ++ "/" ++ filename
      plotDataD =
        map
          ( \(x, y) ->
              ( fromIntegral x :: Double
              , fromIntegral y :: Double
              )
          )
          plotData
      slopeD = fromIntegral slope :: Double
      interceptD = fromIntegral intercept :: Double
      predictedPoints =
        [ ( x
          , slopeD * x + interceptD
          )
        | (x, _) <- plotDataD
        ]
  toFile def outPath $ do
    layout_title .= title
    layout_x_axis . laxis_title .= xTitle
    layout_y_axis . laxis_title .= yTitle
    plot $ points "Data Points" plotDataD
    setColors [opaque (sRGB24 255 0 0)]
    plot $ line "Predicted (model)" [predictedPoints]

-- Generate scatter plot of Value memory vs Data memory (kept for compatibility)
generateScatterPlot
  :: String
  -> String
  -> String
  -> FilePath
  -> [(Integer, Integer)]
  -> Integer
  -> Integer
  -> IO ()
generateScatterPlot title xTitle yTitle filename plotData slope intercept = do
  let plotDataD :: [(Double, Double)]
      plotDataD = map (\(x, y) -> (fromIntegral x :: Double, fromIntegral y :: Double)) plotData
      slopeD = fromIntegral slope :: Double
      interceptD = fromIntegral intercept :: Double

  ensureDataDir
  let outPath = dataOutDir ++ "/" ++ filename

  toFile def outPath $ do
    layout_title .= title
    layout_x_axis . laxis_title .= xTitle
    layout_y_axis . laxis_title .= yTitle
    plot $ points "Memory Usage" plotDataD
    -- Compute model predictions at the same X values as the provided plot data
    let predictedPoints = [(x, slopeD * x + interceptD) | x <- map fst plotDataD]
    setColors [opaque (sRGB24 255 0 0)]
    plot $ line "Predicted (model)" [predictedPoints]
