module PlutusBenchmark.RegressionInteger (integerBestFit) where

import Data.List (minimumBy)
import Data.Maybe (catMaybes)
import Data.Ord (comparing)

--------------------------------------------------------------------------------
-- Constrained Linear Regression -----------------------------------------------

{-| Find best integer (slope, intercept) with non-negativity constraints.
Uses constrained OLS with overestimation bias, then refines with integer search.
Underestimation is penalized more heavily to ensure safe memory costing. -}
integerBestFit :: [(Integer, Integer)] -> (Integer, Integer)
integerBestFit pts
  | null pts = (0, 0)
  | otherwise =
      let ptsD = [(fromIntegral x, fromIntegral y) | (x, y) <- pts]
          penalty = 2.0 -- Underestimation errors weighted 4x more
          (sD, iD) = constrainedOLS penalty ptsD -- Already non-negative

          -- Search neighborhood in non-negative space
          baseS = round sD
          baseI = round iD
          deltaS = max 3 baseS + 5
          deltaI = max 10 (baseI `div` 2) + 10

          -- Only non-negative candidates (neighborhood bounded by 0)
          slopes = [max 0 (baseS - deltaS) .. baseS + deltaS]
          intercepts = [max 0 (baseI - deltaI) .. baseI + deltaI]

          lossFor s i = asymmetricLoss penalty ptsD (fromIntegral s, fromIntegral i)

          candidates = [(s, i, lossFor s i) | s <- slopes, i <- intercepts]
          (bestS, bestI, _) =
            minimumBy (comparing (\(_, _, loss) -> loss)) candidates
       in (bestS, bestI) -- Already guaranteed non-negative

{-| Compute asymmetric loss with underestimation penalty.
Underestimation (predicted < actual) is penalized more heavily than overestimation.
This biases the regression toward safe overestimation for memory costing. -}
asymmetricLoss :: Double -> [(Double, Double)] -> (Double, Double) -> Double
asymmetricLoss penalty pts (slope, intercept) =
  sum
    [ let predicted = slope * x + intercept
          err = y - predicted
       in if err > 0 -- underestimation (predicted < actual) - DANGEROUS
            then (penalty * err) ** 2
            else err ** 2 -- overestimation (predicted >= actual) - SAFE
    | (x, y) <- pts
    ]

{-| Non-negative constrained ordinary least squares with asymmetric loss.
Finds best (slope, intercept) with slope ≥ 0 and intercept ≥ 0.
Considers four cases and chooses the one with minimum asymmetric loss:
  1. Unconstrained OLS (if both coefficients are non-negative)
  2. Through origin: intercept = 0, slope = Σ(xy)/Σ(x²)
  3. Horizontal line: slope = 0, intercept = mean(y)
  4. Both at boundary: (0, 0) - always valid fallback -}
constrainedOLS :: Double -> [(Double, Double)] -> (Double, Double)
constrainedOLS penalty pts
  | null pts = (0, 0)
  | otherwise =
      let
        -- Try unconstrained OLS first
        (sOLS, iOLS) = continuousOLS pts

        -- Helper: compute asymmetric loss for given coefficients
        lossFor s i = asymmetricLoss penalty pts (s, i)

        -- Case 1: Unconstrained (if both non-negative)
        case1 =
          if sOLS >= 0 && iOLS >= 0
            then Just (sOLS, iOLS, lossFor sOLS iOLS)
            else Nothing

        -- Case 2: Through origin (intercept = 0, slope free)
        sOrigin =
          let numerator = sum [x * y | (x, y) <- pts]
              denominator = sum [x * x | (x, _) <- pts]
           in if denominator == 0 then 0 else numerator / denominator
        case2 =
          if sOrigin >= 0
            then Just (sOrigin, 0, lossFor sOrigin 0)
            else Nothing

        -- Case 3: Horizontal line (slope = 0, intercept = mean(y))
        iHoriz = sum (map snd pts) / fromIntegral (length pts)
        case3 = (0, iHoriz, lossFor 0 iHoriz)

        -- Case 4: Both at boundary (always valid)
        case4 = (0, 0, lossFor 0 0)

        -- Choose case with minimum asymmetric loss
        validCases = catMaybes [case1, case2] ++ [case3, case4]
        (bestS, bestI, _) = minimumBy (comparing (\(_, _, loss) -> loss)) validCases
       in
        (bestS, bestI)

--------------------------------------------------------------------------------
-- Unconstrained OLS -----------------------------------------------------------

{-| Standard unconstrained ordinary least squares.
May produce negative coefficients. -}
continuousOLS :: [(Double, Double)] -> (Double, Double)
continuousOLS pts
  | null pts = (0, 0)
  | otherwise =
      let xs = map fst pts
          ys = map snd pts
          n = fromIntegral (length xs)
          sx = sum xs
          sy = sum ys
          sxx = sum (map (\x -> x * x) xs)
          sxy = sum (zipWith (*) xs ys)
          denom = n * sxx - sx * sx
       in if denom == 0
            then (0, sy / n)
            else
              let a = (n * sxy - sx * sy) / denom
                  b = (sy - a * sx) / n
               in (a, b)
