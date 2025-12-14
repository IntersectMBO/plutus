-- editorconfig-checker-disable-file

-- | The types and functions that are common among all ledger Plutus versions.
module PlutusLedgerApi.Common
  ( -- * Script (de)serialization
    SerialisedScript.SerialisedScript
  , SerialisedScript.ScriptForEvaluation
  , SerialisedScript.serialisedScript
  , SerialisedScript.deserialisedScript
  , SerialisedScript.serialiseCompiledCode
  , SerialisedScript.serialiseUPLC
  , SerialisedScript.deserialiseScript
  , SerialisedScript.uncheckedDeserialiseUPLC
  , SerialisedScript.ScriptDecodeError (..)
  , SerialisedScript.ScriptNamedDeBruijn (..)

    -- * Script evaluation
  , Eval.evaluateScriptCounting
  , Eval.evaluateScriptRestricting
  , Eval.evaluateTerm
  , Eval.VerboseMode (..)
  , Eval.LogOutput
  , Eval.EvaluationError (..)

    -- * Network's versioning
    {-| The network's behaviour (and plutus's by extension) can change via /hard forks/,
    which directly correspond to major-number protocol version bumps. -}
  , Versions.MajorProtocolVersion (..)
  , Versions.PlutusLedgerLanguage (..)
  , Versions.Version (..)
  , Versions.builtinsIntroducedIn
  , Versions.builtinsAvailableIn
  , Versions.ledgerLanguageIntroducedIn
  , Versions.ledgerLanguagesAvailableIn

    -- * Protocol Versions
  , Protocol.shelleyPV
  , Protocol.allegraPV
  , Protocol.maryPV
  , Protocol.alonzoPV
  , Protocol.vasilPV
  , Protocol.valentinePV
  , Protocol.changPV
  , Protocol.plominPV
  , Protocol.pv11PV
  , Protocol.knownPVs

    -- * Costing-related types
  , PLC.ExBudget (..)
  , PLC.ExCPU (..)
  , PLC.ExMemory (..)
  , SatInt.SatInt (unSatInt)
  , SatInt.fromSatInt

    -- * Network's costing parameters
    {-| A less drastic approach (that does not rely on a HF)
    to affect the network's (and plutus's by extension) behaviour
    is by tweaking the values of the cost model parameters.

    The network does not associate names to cost model parameters;
    Plutus attaches names to the network's cost model parameters (values)
    either in a raw textual form or typed by a specific plutus version.

    See Note [Cost model parameters] -}
  , PLC.CostModelParams
  , ParamName.toCostModelParams
  , Eval.assertWellFormedCostModelParams
  , ParamName.IsParamName (showParamName, readParamName)
  , ParamName.GenericParamName
  , ParamName.CostModelApplyError (..)
  , ParamName.CostModelApplyWarn (..)

    -- ** Evaluation context
  , Eval.EvaluationContext (..)
  , Eval.mkDynEvaluationContext
  , Eval.toMachineParameters
  -- While not strictly used by the ledger, this is useful for people trying to
  -- reconstruct the term evaluated by the ledger from the arguments, e.g.
  -- for profiling purposes.
  , Eval.mkTermToEvaluate

    -- ** Supporting types used in the context types

    -- *** Builtins
  , TxPrelude.BuiltinByteString
  , TxPrelude.toBuiltin
  , TxPrelude.fromBuiltin
  , TxPrelude.toOpaque
  , TxPrelude.fromOpaque

    -- * Data
  , PLC.Data (..)
  , Builtins.BuiltinData (..)
  , IsData.ToData (..)
  , IsData.FromData (..)
  , IsData.UnsafeFromData (..)
  , IsData.toData
  , IsData.fromData
  , IsData.unsafeFromData
  , Builtins.dataToBuiltinData
  , Builtins.builtinDataToData

    -- * Misc
  , MonadError
  ) where

import PlutusLedgerApi.Common.Eval qualified as Eval
import PlutusLedgerApi.Common.ParamName qualified as ParamName
import PlutusLedgerApi.Common.ProtocolVersions qualified as Protocol
import PlutusLedgerApi.Common.SerialisedScript qualified as SerialisedScript
import PlutusLedgerApi.Common.Versions qualified as Versions

import PlutusTx.Builtins.Internal qualified as Builtins
import PlutusTx.IsData.Class qualified as IsData
import PlutusTx.Prelude qualified as TxPrelude

import PlutusCore.Data qualified as PLC
import PlutusCore.Evaluation.Machine.CostModelInterface qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget qualified as PLC
import PlutusCore.Evaluation.Machine.ExMemory qualified as PLC

import Control.Monad.Except (MonadError)
import Data.SatInt qualified as SatInt
