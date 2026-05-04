{-# LANGUAGE ViewPatterns #-}

-- Produce an optimization report.
module PlutusCore.Executable.OptimizerReport
  ( ReportEntry (..)
  , OptimizerReport
  , buildReport
  , printReport
  ) where

import PlutusCore.Evaluation.Machine.ExBudget (ExBudget (..))
import PlutusCore.Evaluation.Machine.ExMemory (ExCPU (..), ExMemory (..))
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Transform.Certify.Trace
  ( Optimization (stage)
  , OptimizerTrace (optimizerTrace)
  , allASTs
  )

import Data.Foldable
import Data.Maybe
import Data.SatInt
import System.IO (Handle, hPutStrLn)
import Text.Printf (printf)

data ReportEntry = ReportEntry
  { rePassName :: Maybe String
  -- ^ `Nothing` for the first entry, `Just` for all other entries.
  , reAstSize :: Integer
  , reCost :: Maybe (Either String ExBudget)
  -- ^ `Nothing` means evaluation wans't requested.  `Left` means evaluation failed.
  }

type OptimizerReport = [ReportEntry]

-- FIXME: we need a lot of `reverse` here because `OptimizerTrace` contains the passes
-- in reverse order.
buildReport
  :: OptimizerTrace UPLC.Name uni fun a
  -> [(Maybe err, ExBudget)]
  -> OptimizerReport
buildReport trace (reverse -> costs) =
  zipWith3 ReportEntry passNames sizes mCosts
  where
    asts = reverse (allASTs trace)
    passNames =
      Nothing : (Just . either show show . stage <$> reverse (optimizerTrace trace))
    sizes = UPLC.unAstSize . UPLC.termAstSize <$> asts
    mCosts = case costs of
      [] -> repeat Nothing -- evaluation wasn't requested
      cs -> Just . classifyCost <$> cs
    classifyCost (Just _, _) = Left "<failed>"
    classifyCost (Nothing, b) = Right b

printReport :: Handle -> OptimizerReport -> IO ()
printReport h entries = do
  let withCosts = any (isJust . reCost) entries
      put = hPutStrLn h
  put "=== UPLC optimization report ==="
  put (header withCosts)
  put (replicate (length (header withCosts)) '-')
  traverse_ put $
    zipWith (formatEntry withCosts) (Nothing : (Just <$> entries)) entries
  put ""

-- Column widths.
passColW, sizeColW, cpuColW, memColW :: Int
passColW = 20
sizeColW = 8
cpuColW = 15
memColW = 15

header :: Bool -> String
header False =
  printf
    "%-*s %*s %*s"
    passColW
    "Pass"
    sizeColW
    "size"
    sizeColW
    "ΔSize"
header True =
  printf
    "%-*s %*s %*s %*s %*s %*s %*s"
    passColW
    "Pass"
    sizeColW
    "size"
    sizeColW
    "ΔSize"
    cpuColW
    "CPU"
    cpuColW
    "ΔCPU"
    memColW
    "Mem"
    memColW
    "ΔMem"

formatEntry :: Bool -> Maybe ReportEntry -> ReportEntry -> String
formatEntry withCosts mPrev cur =
  let name = maybe "<initial>" id (rePassName cur)
      sz = reAstSize cur
      dSz = case mPrev of
        Just p -> showSigned (sz - reAstSize p)
        Nothing -> ""
      sizeBlock =
        printf
          "%-*s %*d %*s"
          passColW
          name
          sizeColW
          sz
          sizeColW
          dSz
          :: String
   in if withCosts
        then sizeBlock ++ " " ++ costBlock mPrev cur
        else sizeBlock

costBlock :: Maybe ReportEntry -> ReportEntry -> String
costBlock mPrev cur = case reCost cur of
  Nothing -> spread "-" "" "-" ""
  Just (Left tag) -> spread tag "" "" ""
  Just (Right (ExBudget (ExCPU cpu) (ExMemory mem))) ->
    let mPrevB =
          mPrev >>= \r -> case reCost r of
            Just (Right b) -> Just b
            _ -> Nothing
        (dCpu, dMem) = case mPrevB of
          Just (ExBudget (ExCPU pc) (ExMemory pm)) ->
            ( showSigned (fromSatInt cpu - fromSatInt pc :: Int)
            , showSigned (fromSatInt mem - fromSatInt pm :: Int)
            )
          Nothing -> ("", "")
     in printf
          "%*d %*s %*d %*s"
          cpuColW
          (fromSatInt cpu :: Int)
          cpuColW
          dCpu
          memColW
          (fromSatInt mem :: Int)
          memColW
          dMem
  where
    spread c dC m dM =
      printf
        "%*s %*s %*s %*s"
        cpuColW
        c
        cpuColW
        dC
        memColW
        m
        memColW
        dM

showSigned :: (Ord a, Num a, Show a) => a -> String
showSigned n
  | n > 0 = '+' : show n
  | otherwise = show n
