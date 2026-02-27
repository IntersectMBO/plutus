{-# LANGUAGE ImplicitParams #-}

module Mode.PrintCostModel
  ( runPrintCostModel
  ) where

import Common
import GetOpt
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults as PLC

import Data.Aeson.Encode.Pretty as Aeson
import Data.ByteString.Lazy qualified as BSL
import Data.Maybe

runPrintCostModel :: (?opts :: Opts) => IO ()
runPrintCostModel = do
  -- MAYBE: move to print-cost-model executable impl. which is much prettier
  printE "Cost model of latest plutus version:"
  -- TODO: add a semantic variant here to get the right machine parameters
  let params = fromJust PLC.defaultCostModelParamsForTesting

  BSL.putStr $ Aeson.encodePretty params
  putStrLn "" -- just for reading clarity
