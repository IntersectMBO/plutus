{-# LANGUAGE PatternSynonyms #-}

-- | The data-backed type interface to Plutus V1 for the ledger.
module PlutusLedgerApi.Data.V1
  ( -- * Scripts
    Common.SerialisedScript
  , Common.ScriptForEvaluation
  , Common.serialisedScript
  , Common.deserialisedScript
  , Common.serialiseCompiledCode
  , Common.serialiseUPLC
  , V1SOP.deserialiseScript
  , Common.uncheckedDeserialiseUPLC

    -- * Running scripts
  , V1SOP.evaluateScriptRestricting
  , V1SOP.evaluateScriptCounting

    -- ** Protocol version
  , Common.MajorProtocolVersion (..)

    -- ** Verbose mode and log output
  , Common.VerboseMode (..)
  , Common.LogOutput

    -- * Costing-related types
  , Common.ExBudget (..)
  , Common.ExCPU (..)
  , Common.ExMemory (..)
  , Common.SatInt (Common.unSatInt)
  , Common.fromSatInt

    -- ** Cost model
  , EvaluationContext.EvaluationContext
  , EvaluationContext.mkEvaluationContext
  , ParamName.ParamName (..)
  , EvaluationContext.CostModelApplyError (..)
  , EvaluationContext.CostModelParams
  , EvaluationContext.assertWellFormedCostModelParams

    -- * Context types
  , Contexts.ScriptContext
  , pattern Contexts.ScriptContext
  , Contexts.scriptContextTxInfo
  , Contexts.scriptContextPurpose
  , Contexts.ScriptPurpose
  , pattern Contexts.Minting
  , pattern Contexts.Spending
  , pattern Contexts.Rewarding
  , pattern Contexts.Certifying

    -- ** Supporting types used in the context types

    -- *** ByteStrings
  , Common.BuiltinByteString
  , Common.toBuiltin
  , Common.fromBuiltin

    -- *** Bytes
  , V1SOP.LedgerBytes (..)
  , V1SOP.fromBytes

    -- *** Certificates
  , DCert.DCert
  , pattern DCert.DCertDelegRegKey
  , pattern DCert.DCertDelegDeRegKey
  , pattern DCert.DCertDelegDelegate
  , pattern DCert.DCertPoolRegister
  , pattern DCert.DCertPoolRetire
  , pattern DCert.DCertGenesis
  , pattern DCert.DCertMir

    -- *** Credentials
  , Credential.StakingCredential
  , pattern Credential.StakingHash
  , pattern Credential.StakingPtr
  , Credential.Credential
  , pattern Credential.PubKeyCredential
  , pattern Credential.ScriptCredential

    -- *** Value
  , Value.Value (..)
  , Value.CurrencySymbol (..)
  , Value.TokenName (..)
  , Value.singleton
  , Value.unionWith
  , Value.adaSymbol
  , Value.adaToken
  , Value.Lovelace (..)
  , Value.AssetClass (..)
  , Value.assetClass
  , Value.assetClassValue
  , Value.assetClassValueOf
  , Value.currencySymbol
  , Value.currencySymbolValueOf
  , Value.flattenValue
  , Value.geq
  , Value.gt
  , Value.isZero
  , Value.leq
  , Value.lovelaceValue
  , Value.lovelaceValueOf
  , Value.lt
  , Value.scale
  , Value.split
  , Value.symbols
  , Value.tokenName
  , Value.unsafeLovelaceValueOf
  , Value.valueOf
  , Value.withCurrencySymbol

    -- *** Time
  , Time.POSIXTime (..)
  , Time.POSIXTimeRange

    -- *** Types for representing transactions
  , Address.Address
  , pattern Address.Address
  , Address.addressCredential
  , Address.addressStakingCredential
  , V1SOP.PubKeyHash (..)
  , Contexts.TxId (..)
  , Contexts.TxInfo
  , pattern Contexts.TxInfo
  , Contexts.txInfoInputs
  , Contexts.txInfoOutputs
  , Contexts.txInfoFee
  , Contexts.txInfoMint
  , Contexts.txInfoDCert
  , Contexts.txInfoWdrl
  , Contexts.txInfoValidRange
  , Contexts.txInfoSignatories
  , Contexts.txInfoData
  , Contexts.txInfoId
  , Contexts.TxOut
  , pattern Contexts.TxOut
  , Contexts.txOutAddress
  , Contexts.txOutValue
  , Contexts.txOutDatumHash
  , Contexts.TxOutRef
  , pattern Contexts.TxOutRef
  , Contexts.txOutRefId
  , Contexts.txOutRefIdx
  , Contexts.TxInInfo
  , pattern Contexts.TxInInfo
  , Contexts.txInInfoOutRef
  , Contexts.txInInfoResolved

    -- *** Intervals
  , Interval.Interval
  , pattern Interval.Interval
  , Interval.ivFrom
  , Interval.ivTo
  , Interval.Extended
  , pattern Interval.NegInf
  , pattern Interval.PosInf
  , pattern Interval.Finite
  , Interval.Closure
  , Interval.UpperBound
  , pattern Interval.UpperBound
  , Interval.LowerBound
  , pattern Interval.LowerBound
  , Interval.always
  , Interval.from
  , Interval.to
  , Interval.lowerBound
  , Interval.upperBound
  , Interval.strictLowerBound
  , Interval.strictUpperBound
  , Interval.inclusiveLowerBound
  , Interval.inclusiveUpperBound

    -- *** Newtypes and hash types
  , V1SOP.ScriptHash (..)
  , V1SOP.Redeemer (..)
  , V1SOP.RedeemerHash (..)
  , V1SOP.Datum (..)
  , V1SOP.DatumHash (..)

    -- * Data
  , Common.Data (..)
  , Common.BuiltinData (..)
  , Common.ToData (..)
  , Common.FromData (..)
  , Common.UnsafeFromData (..)
  , Common.toData
  , Common.fromData
  , Common.dataToBuiltinData
  , Common.builtinDataToData

    -- * Errors
  , Common.EvaluationError (..)
  , Common.ScriptDecodeError (..)
  ) where

import PlutusLedgerApi.Common qualified as Common
import PlutusLedgerApi.V1 qualified as V1SOP
import PlutusLedgerApi.V1.Data.Address qualified as Address
import PlutusLedgerApi.V1.Data.Contexts qualified as Contexts
import PlutusLedgerApi.V1.Data.Credential qualified as Credential
import PlutusLedgerApi.V1.Data.DCert qualified as DCert
import PlutusLedgerApi.V1.Data.Interval qualified as Interval
import PlutusLedgerApi.V1.Data.Time qualified as Time
import PlutusLedgerApi.V1.Data.Value qualified as Value
import PlutusLedgerApi.V1.EvaluationContext qualified as EvaluationContext
import PlutusLedgerApi.V1.ParamName qualified as ParamName

-- See Note [Abstract types in the ledger API]
