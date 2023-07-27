-- editorconfig-checker-disable-file
module PlutusLedgerApi.Test.EvaluationContext
    ( costModelParamsForTesting
    , evalCtxForTesting
    ) where

import PlutusCore.Evaluation.Machine.CostModelInterface as Plutus
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults qualified as Plutus
import PlutusLedgerApi.Common
import PlutusPrelude

import Data.Either.Extras
import Data.Maybe

{-| only for testing purposes: The default, raw cost model params.

Note: It always reflects the latest, in-development Plutus version.
-}
costModelParamsForTesting :: Plutus.CostModelParams
costModelParamsForTesting = fromJust Plutus.defaultCostModelParams

{- | only for testing purposes: get an evaluation context by re-applying the
extracted default cost model parameters (resulting in no change to params).
An alternative implementation would be to pass an empty map of params.

Note: It reflects only the latest, in-development Plutus version.
-}
evalCtxForTesting :: EvaluationContext
evalCtxForTesting = unsafeFromEither $ mkDynEvaluationContext def costModelParamsForTesting
