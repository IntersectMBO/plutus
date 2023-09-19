-- | The types and functions that are common among all ledger Plutus versions.
module PlutusLedgerApi.Common
    ( -- * Script (de)serialization
      SerialisedScript
    , ScriptForEvaluation
    , serialisedScript
    , deserialisedScript
    , serialiseCompiledCode
    , serialiseUPLC
    , deserialiseScript
    , uncheckedDeserialiseUPLC
    , ScriptDecodeError (..)

      -- * Script evaluation
    , evaluateScriptCounting
    , evaluateScriptRestricting
    , evaluateTerm
    , VerboseMode (..)
    , LogOutput
    , EvaluationError (..)
    -- reexport Data & ExBudget for convenience to upstream users
    , PlutusCore.Data (..)
    , PlutusCore.ExBudget (..)

      -- * Network's versioning
      {-| The network's behaviour (and plutus's by extension) can change via /hard forks/,
      which directly correspond to major-number protocol version bumps.
      -}
    , MajorProtocolVersion (..)
    , PlutusLedgerLanguage (..)
    , Version (..)
    , builtinsIntroducedIn
    , builtinsAvailableIn
    , ledgerLanguageIntroducedIn
    , ledgerLanguagesAvailableIn

      -- * Network's costing parameters
      {-| A less drastic approach (that does not rely on a HF)
      to affect the network's (and plutus's by extension) behaviour
      is by tweaking the values of the cost model parameters.

      The network does not associate names to cost model parameters;
      Plutus attaches names to the network's cost model parameters (values)
      either in a raw textual form or typed by a specific plutus version.

      See Note [Cost model parameters]
      -}
    , CostModelParams
    , toCostModelParams
    , assertWellFormedCostModelParams
    , IsParamName (showParamName, readParamName)
    , GenericParamName
    , CostModelApplyError (..)
    , CostModelApplyWarn (..)

      -- ** Evaluation context
    , EvaluationContext (..)
    , mkDynEvaluationContext
    , toMachineParameters
    -- While not strictly used by the ledger, this is useful for people trying to
    -- reconstruct the term evaluated by the ledger from the arguments, e.g.
    -- for profiling purposes.
    , mkTermToEvaluate
    ) where

import PlutusCore.Data as PlutusCore (Data (..))
import PlutusCore.Evaluation.Machine.CostModelInterface (CostModelParams)
import PlutusCore.Evaluation.Machine.ExBudget as PlutusCore (ExBudget (..))
import PlutusLedgerApi.Common.Eval
import PlutusLedgerApi.Common.ParamName
import PlutusLedgerApi.Common.SerialisedScript
import PlutusLedgerApi.Common.Versions
