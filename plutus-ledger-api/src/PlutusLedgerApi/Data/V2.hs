{-# LANGUAGE PatternSynonyms #-}

-- | The data-backed type interface to Plutus V2 for the ledger.
module PlutusLedgerApi.Data.V2
  ( -- * Scripts
    Common.SerialisedScript
  , Common.ScriptForEvaluation
  , Common.serialisedScript
  , Common.deserialisedScript
  , Common.serialiseCompiledCode
  , Common.serialiseUPLC
  , V2SOP.deserialiseScript
  , Common.uncheckedDeserialiseUPLC

    -- * Running scripts
  , V2SOP.evaluateScriptRestricting
  , V2SOP.evaluateScriptCounting

    -- ** Protocol version
  , Common.MajorProtocolVersion (..)

    -- ** Verbose mode and log output
  , Common.VerboseMode (..)
  , Common.LogOutput

    -- * Costing-related types
  , Common.ExBudget (..)
  , V1.ExCPU (..)
  , V1.ExMemory (..)
  , V1.SatInt (unSatInt)
  , V1.fromSatInt

    -- ** Cost model
  , Common.EvaluationContext
  , EvaluationContext.mkEvaluationContext
  , ParamName.ParamName (..)
  , Common.CostModelApplyError (..)
  , Common.CostModelParams
  , Common.assertWellFormedCostModelParams

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

    -- *** Builtins
  , Common.BuiltinByteString
  , Common.toBuiltin
  , Common.fromBuiltin
  , Common.toOpaque
  , Common.fromOpaque

    -- *** Bytes
  , V1.LedgerBytes (..)
  , V1.fromBytes

    -- *** Certificates
  , V1.DCert
  , pattern V1.DCertDelegRegKey
  , pattern V1.DCertDelegDeRegKey
  , pattern V1.DCertDelegDelegate
  , pattern V1.DCertPoolRegister
  , pattern V1.DCertPoolRetire
  , pattern V1.DCertGenesis
  , pattern V1.DCertMir

    -- *** Credentials
  , V1.StakingCredential
  , pattern V1.StakingHash
  , pattern V1.StakingPtr
  , V1.Credential
  , pattern V1.PubKeyCredential
  , pattern V1.ScriptCredential

    -- *** Value
  , V1.Value (..)
  , V1.CurrencySymbol (..)
  , V1.TokenName (..)
  , V1.singleton
  , V1.unionWith
  , V1.adaSymbol
  , V1.adaToken
  , V1.Lovelace (..)
  , V1.AssetClass (..)
  , V1.assetClass
  , V1.assetClassValue
  , V1.assetClassValueOf
  , V1.currencySymbol
  , V1.currencySymbolValueOf
  , V1.flattenValue
  , V1.geq
  , V1.gt
  , V1.isZero
  , V1.leq
  , V1.lovelaceValue
  , V1.lovelaceValueOf
  , V1.lt
  , V1.scale
  , V1.split
  , V1.symbols
  , V1.tokenName
  , V1.unsafeLovelaceValueOf
  , V1.valueOf
  , V1.withCurrencySymbol

    -- *** Time
  , V1.POSIXTime (..)
  , V1.POSIXTimeRange

    -- *** Types for representing transactions
  , V1.Address
  , pattern V1.Address
  , V1.addressCredential
  , V1.addressStakingCredential
  , V1.PubKeyHash (..)
  , Tx.TxId (..)
  , Contexts.TxInfo
  , pattern Contexts.TxInfo
  , Contexts.txInfoInputs
  , Contexts.txInfoReferenceInputs
  , Contexts.txInfoOutputs
  , Contexts.txInfoFee
  , Contexts.txInfoMint
  , Contexts.txInfoDCert
  , Contexts.txInfoWdrl
  , Contexts.txInfoValidRange
  , Contexts.txInfoSignatories
  , Contexts.txInfoRedeemers
  , Contexts.txInfoData
  , Contexts.txInfoId
  , Tx.TxOut
  , pattern Tx.TxOut
  , Tx.txOutAddress
  , Tx.txOutValue
  , Tx.txOutDatum
  , Tx.txOutReferenceScript
  , Tx.TxOutRef
  , pattern Tx.TxOutRef
  , Tx.txOutRefId
  , Tx.txOutRefIdx
  , Contexts.TxInInfo
  , pattern Contexts.TxInInfo
  , Contexts.txInInfoOutRef
  , Contexts.txInInfoResolved
  , Tx.OutputDatum
  , pattern Tx.NoOutputDatum
  , pattern Tx.OutputDatum
  , pattern Tx.OutputDatumHash

    -- *** Intervals
  , V1.Interval
  , pattern V1.Interval
  , V1.ivFrom
  , V1.ivTo
  , V1.Extended
  , pattern V1.NegInf
  , pattern V1.PosInf
  , pattern V1.Finite
  , V1.Closure
  , V1.UpperBound
  , pattern V1.UpperBound
  , V1.LowerBound
  , pattern V1.LowerBound
  , V1.always
  , V1.from
  , V1.to
  , V1.lowerBound
  , V1.upperBound
  , V1.strictLowerBound
  , V1.strictUpperBound
  , V1.inclusiveLowerBound
  , V1.inclusiveUpperBound

    -- *** Association maps
  , Map
  , unsafeFromDataList
  , unsafeFromBuiltinList
  , unsafeFromSOPList
  , safeFromSOPList
  , toSOPList
  , toBuiltinList

    -- *** Newtypes and hash types
  , V1.ScriptHash (..)
  , V1.Redeemer (..)
  , V1.RedeemerHash (..)
  , V1.Datum (..)
  , V1.DatumHash (..)

    -- * Data
  , Common.Data (..)
  , Common.BuiltinData (..)
  , Common.ToData (..)
  , Common.FromData (..)
  , Common.UnsafeFromData (..)
  , Common.toData
  , Common.fromData
  , Common.unsafeFromData
  , Common.dataToBuiltinData
  , Common.builtinDataToData

    -- * Errors
  , Common.MonadError
  , Common.EvaluationError (..)
  , Common.ScriptDecodeError (..)
  ) where

import PlutusLedgerApi.Common qualified as Common
import PlutusLedgerApi.Data.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2SOP
import PlutusLedgerApi.V2.Data.Contexts qualified as Contexts
import PlutusLedgerApi.V2.Data.Tx qualified as Tx
import PlutusLedgerApi.V2.EvaluationContext qualified as EvaluationContext
import PlutusLedgerApi.V2.ParamName qualified as ParamName

import PlutusTx.Data.AssocMap
  ( Map
  , safeFromSOPList
  , toBuiltinList
  , toSOPList
  , unsafeFromBuiltinList
  , unsafeFromDataList
  , unsafeFromSOPList
  )
