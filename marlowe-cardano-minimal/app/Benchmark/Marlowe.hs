
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RecordWildCards #-}


module Benchmark.Marlowe (
  executeBenchmark
, evaluationContext
) where


import Benchmark.Marlowe.Types (Benchmark (..))

import Control.Monad.Except (runExcept)
import Control.Monad.Writer (runWriterT)
import Data.Bifunctor (bimap)
import Data.Maybe (fromJust)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCostModelParams)

import Data.Map.Strict qualified as M
import PlutusLedgerApi.V2 qualified as V2


executeBenchmark
  :: V2.SerialisedScript
  -> Benchmark
  -> Either String (V2.LogOutput, Either V2.EvaluationError V2.ExBudget)
executeBenchmark serialisedValidator Benchmark{..} =
  case evaluationContext of
   Left message -> Left message
   Right ec ->
    Right
      $ V2.evaluateScriptCounting (V2.ProtocolVersion 8 0) V2.Verbose ec serialisedValidator
        [bDatum, bRedeemer, V2.toData bScriptContext]


evaluationContext :: Either String V2.EvaluationContext
evaluationContext =
  let
    costParams = M.elems $ fromJust defaultCostModelParams
    costModel = take (length ([minBound..maxBound] :: [V2.ParamName])) costParams
  in
    bimap show fst . runExcept . runWriterT $ V2.mkEvaluationContext costModel

