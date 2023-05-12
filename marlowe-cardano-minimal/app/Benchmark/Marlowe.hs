
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}


module Benchmark.Marlowe (
  executeBenchmark
, evaluationContext
, readBenchmark
, readBenchmarks
, printBenchmark
, printResult
, tabulateResults
) where


import Benchmark.Marlowe.Types (Benchmark (..))
import Codec.Serialise (deserialise)
import Control.Monad.Except (runExcept)
import Control.Monad.Writer (runWriterT)
import Data.Bifunctor (bimap)
import Data.Maybe (fromJust)
import Language.Marlowe.Core.V1.Semantics (MarloweData)
import Language.Marlowe.Scripts (MarloweInput)
import Paths_marlowe_cardano_minimal (getDataDir)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCostModelParams)
import PlutusLedgerApi.V2 (Data (Constr, I), EvaluationContext, EvaluationError,
                           ExBudget (ExBudget, exBudgetCPU, exBudgetMemory), ExCPU (ExCPU),
                           ExMemory (ExMemory), LogOutput, ParamName (..), ProtocolVersion (..),
                           ScriptContext (scriptContextTxInfo), ScriptHash, SerialisedScript,
                           TxInfo (txInfoId), VerboseMode (Verbose), evaluateScriptCounting,
                           fromData, mkEvaluationContext, toData)
import System.Directory (listDirectory)
import System.FilePath ((</>))

import Data.ByteString.Lazy qualified as LBS (readFile)
import Data.Map qualified as M (elems)


executeBenchmark
  :: SerialisedScript
  -> Benchmark
  -> Either String (LogOutput, Either EvaluationError ExBudget)
executeBenchmark serialisedValidator Benchmark{..} =
  case evaluationContext of
   Left message -> Left message
   Right ec ->
    Right
      $ evaluateScriptCounting (ProtocolVersion 8 0) Verbose ec serialisedValidator
        [bDatum, bRedeemer, toData bScriptContext]


evaluationContext :: Either String EvaluationContext
evaluationContext =
  let
    -- Note: These default cost model parameters are identical to those from commit
    --       6ed578b592f46afc0e77f4d19e5955a6eb439ba4, which is where the reference costs used
    --       for comparison were measured.
    costParams = M.elems $ fromJust defaultCostModelParams
    costModel = take (length ([minBound..maxBound] :: [ParamName])) costParams
  in
    bimap show fst . runExcept . runWriterT $ mkEvaluationContext costModel


readBenchmarks
  :: FilePath
  -> IO (Either String [Benchmark])
readBenchmarks subfolder =
  do
    folder <- (</> subfolder) <$> getDataDir :: IO FilePath
    files <- fmap (folder </>) <$> listDirectory folder :: IO [FilePath]
    sequence <$> mapM readBenchmark files


readBenchmark
  :: FilePath
  -> IO (Either String Benchmark)
readBenchmark filename =
  do
    payload <- LBS.readFile filename
    pure
      $ case deserialise payload of
        Constr 0 [bDatum, bRedeemer, scriptContext, I cpu, I memory] ->
             do
               bScriptContext <-
                 maybe (Left "Failed deserializing script context") pure
                   $ fromData scriptContext
               let
                 bReferenceCost = Just $ ExBudget (fromInteger cpu) (fromInteger memory)
               pure Benchmark{..}
        _ -> Left "Failed deserializing benchmark file."


printBenchmark
  :: Benchmark
  -> IO ()
printBenchmark Benchmark{..} =
  do
    putStrLn ""
    print (fromData bDatum :: Maybe MarloweData)
    putStrLn ""
    print (fromData bRedeemer :: Maybe MarloweInput)
    putStrLn ""
    print bScriptContext
    putStrLn ""
    print bReferenceCost


printResult
  :: SerialisedScript
  -> Benchmark
  -> IO ()
printResult validator benchmark =
  case executeBenchmark validator benchmark of
    Right (_, Right budget) ->
      putStrLn ("actual = " <> show budget <> " vs expected = " <> show (bReferenceCost benchmark))
    Right (logs, Left msg) -> print (msg, logs)
    Left msg -> print msg


tabulateResults
  :: String
  -> ScriptHash
  -> SerialisedScript
  -> [Benchmark]
  -> [[String]]
tabulateResults name hash validator benchmarks =
  let
    na = "NA"
    unExCPU (ExCPU n) = n
    unExMemory (ExMemory n) = n
  in
    ["Validator", "Script", "TxId"]
       : ["Measured CPU", "Measured Memory", "Reference CPU", "Reference Memory", "Message"]
      : [
          [name, show hash, show txId] <>
            case executeBenchmark validator benchmark of
              Right (_, Right budget) ->
                [
                  show . unExCPU $ exBudgetCPU budget
                , show . unExMemory $ exBudgetMemory budget
                , cpuRef
                , memoryRef
                , mempty
                ]
              Right (logs, Left msg) -> [na, na, cpuRef, memoryRef, show (logs, msg)]
              Left msg -> [na, na, cpuRef, memoryRef, show msg]
        |
          benchmark@Benchmark{..} <- benchmarks
        , let txId = txInfoId $ scriptContextTxInfo bScriptContext
              cpuRef = maybe na (show . unExCPU . exBudgetCPU) bReferenceCost
              memoryRef = maybe na (show . unExMemory . exBudgetMemory) bReferenceCost
        ]
