{-# LANGUAGE PatternSynonyms #-}

-- | The interface to Plutus V3 for the ledger.
module PlutusLedgerApi.Data.V3
  ( -- * Scripts
    Common.SerialisedScript
  , Common.ScriptForEvaluation
  , Common.serialisedScript
  , Common.deserialisedScript
  , Common.serialiseCompiledCode
  , Common.serialiseUPLC
  , deserialiseScript
  , Common.uncheckedDeserialiseUPLC

    -- * Running scripts
  , evaluateScriptRestricting
  , evaluateScriptCounting

    -- ** CIP-1694
  , Contexts.ColdCommitteeCredential (..)
  , Contexts.HotCommitteeCredential (..)
  , Contexts.DRepCredential (..)
  , Contexts.DRep
  , pattern Contexts.DRep
  , pattern Contexts.DRepAlwaysAbstain
  , pattern Contexts.DRepAlwaysNoConfidence
  , Contexts.Delegatee
  , pattern Contexts.DelegStake
  , pattern Contexts.DelegVote
  , pattern Contexts.DelegStakeVote
  , Contexts.TxCert
  , pattern Contexts.TxCertRegStaking
  , pattern Contexts.TxCertUnRegStaking
  , pattern Contexts.TxCertDelegStaking
  , pattern Contexts.TxCertRegDeleg
  , pattern Contexts.TxCertRegDRep
  , pattern Contexts.TxCertUpdateDRep
  , pattern Contexts.TxCertUnRegDRep
  , pattern Contexts.TxCertPoolRegister
  , pattern Contexts.TxCertPoolRetire
  , pattern Contexts.TxCertAuthHotCommittee
  , pattern Contexts.TxCertResignColdCommittee
  , Contexts.Voter
  , pattern Contexts.CommitteeVoter
  , pattern Contexts.DRepVoter
  , pattern Contexts.StakePoolVoter
  , Contexts.Vote
  , pattern Contexts.VoteNo
  , pattern Contexts.VoteYes
  , pattern Contexts.Abstain
  , Contexts.GovernanceActionId
  , Contexts.gaidTxId
  , Contexts.gaidGovActionIx
  , Contexts.Committee
  , pattern Contexts.Committee
  , Contexts.committeeMembers
  , Contexts.committeeQuorum
  , Contexts.Constitution (..)
  , Contexts.ProtocolVersion
  , pattern Contexts.ProtocolVersion
  , Contexts.pvMajor
  , Contexts.pvMinor
  , Contexts.GovernanceAction
  , pattern Contexts.ParameterChange
  , pattern Contexts.HardForkInitiation
  , pattern Contexts.TreasuryWithdrawals
  , pattern Contexts.NoConfidence
  , pattern Contexts.UpdateCommittee
  , pattern Contexts.NewConstitution
  , pattern Contexts.InfoAction
  , Contexts.ChangedParameters (..)
  , Contexts.ProposalProcedure
  , pattern Contexts.ProposalProcedure
  , Contexts.ppDeposit
  , Contexts.ppReturnAddr
  , Contexts.ppGovernanceAction

    -- ** Protocol version
  , Common.MajorProtocolVersion (..)

    -- ** Verbose mode and log output
  , Common.VerboseMode (..)
  , Common.LogOutput

    -- * Costing-related types
  , Common.ExBudget (..)
  , V2.ExCPU (..)
  , V2.ExMemory (..)
  , V2.SatInt (V2.unSatInt)
  , V2.fromSatInt

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
  , Contexts.scriptContextRedeemer
  , Contexts.scriptContextScriptInfo
  , Contexts.ScriptPurpose
  , pattern Contexts.Minting
  , pattern Contexts.Spending
  , pattern Contexts.Rewarding
  , pattern Contexts.Certifying
  , pattern Contexts.Voting
  , pattern Contexts.Proposing
  , Contexts.ScriptInfo
  , pattern Contexts.MintingScript
  , pattern Contexts.SpendingScript
  , pattern Contexts.RewardingScript
  , pattern Contexts.CertifyingScript
  , pattern Contexts.VotingScript
  , pattern Contexts.ProposingScript

    -- ** Supporting types used in the context types

    -- *** Builtins
  , Common.BuiltinByteString
  , Common.toBuiltin
  , Common.fromBuiltin
  , Common.toOpaque
  , Common.fromOpaque

    -- *** Bytes
  , V2.LedgerBytes (..)
  , V2.fromBytes

    -- *** Credentials
  , V2.StakingCredential
  , pattern V2.StakingHash
  , pattern V2.StakingPtr
  , V2.Credential
  , pattern V2.PubKeyCredential
  , pattern V2.ScriptCredential

    -- *** Value
  , V2.Value (..)
  , V2.CurrencySymbol (..)
  , V2.TokenName (..)
  , V2.singleton
  , V2.unionWith
  , V2.adaSymbol
  , V2.adaToken
  , V2.Lovelace (..)

    -- *** Mint Value
  , MintValue.MintValue
  , MintValue.emptyMintValue
  , MintValue.mintValueToMap
  , MintValue.mintValueMinted
  , MintValue.mintValueBurned

    -- *** Time
  , V2.POSIXTime (..)
  , V2.POSIXTimeRange

    -- *** Types for representing transactions
  , V2.Address
  , pattern V2.Address
  , V2.addressCredential
  , V2.addressStakingCredential
  , V2.PubKeyHash (..)
  , Tx.TxId (..)
  , Contexts.TxInfo
  , pattern Contexts.TxInfo
  , Contexts.txInfoInputs
  , Contexts.txInfoReferenceInputs
  , Contexts.txInfoOutputs
  , Contexts.txInfoFee
  , Contexts.txInfoMint
  , Contexts.txInfoTxCerts
  , Contexts.txInfoWdrl
  , Contexts.txInfoValidRange
  , Contexts.txInfoSignatories
  , Contexts.txInfoRedeemers
  , Contexts.txInfoData
  , Contexts.txInfoId
  , Contexts.txInfoVotes
  , Contexts.txInfoProposalProcedures
  , Contexts.txInfoCurrentTreasuryAmount
  , Contexts.txInfoTreasuryDonation
  , V2.TxOut
  , pattern V2.TxOut
  , V2.txOutAddress
  , V2.txOutValue
  , V2.txOutDatum
  , V2.txOutReferenceScript
  , Tx.TxOutRef
  , pattern Tx.TxOutRef
  , Tx.txOutRefId
  , Tx.txOutRefIdx
  , Contexts.TxInInfo
  , pattern Contexts.TxInInfo
  , Contexts.txInInfoOutRef
  , Contexts.txInInfoResolved
  , V2.OutputDatum
  , pattern V2.NoOutputDatum
  , pattern V2.OutputDatum
  , pattern V2.OutputDatumHash

    -- *** Intervals
  , V2.Interval
  , pattern V2.Interval
  , V2.ivFrom
  , V2.ivTo
  , V2.Extended
  , pattern V2.NegInf
  , pattern V2.PosInf
  , pattern V2.Finite
  , V2.Closure
  , V2.UpperBound
  , pattern V2.UpperBound
  , V2.LowerBound
  , pattern V2.LowerBound
  , V2.always
  , V2.from
  , V2.to
  , V2.lowerBound
  , V2.upperBound
  , V2.strictLowerBound
  , V2.strictUpperBound

    -- *** Ratio
  , Ratio.Rational
  , Ratio.ratio
  , Ratio.unsafeRatio
  , Ratio.numerator
  , Ratio.denominator
  , Ratio.fromHaskellRatio
  , Ratio.toHaskellRatio

    -- *** Association maps
  , V2.Map
  , V2.unsafeFromSOPList

    -- *** Newtypes and hash types
  , V2.ScriptHash (..)
  , V2.Redeemer (..)
  , V2.RedeemerHash (..)
  , V2.Datum (..)
  , V2.DatumHash (..)

    -- * Data
  , V2.Data (..)
  , V2.BuiltinData (..)
  , V2.ToData (..)
  , V2.FromData (..)
  , V2.UnsafeFromData (..)
  , V2.toData
  , V2.fromData
  , V2.unsafeFromData
  , V2.dataToBuiltinData
  , V2.builtinDataToData

    -- * Errors
  , Common.MonadError
  , V2.EvaluationError (..)
  , V2.ScriptDecodeError (..)
  ) where

import PlutusLedgerApi.Common qualified as Common
import PlutusLedgerApi.Data.V2 qualified as V2
import PlutusLedgerApi.V3.Data.Contexts qualified as Contexts
import PlutusLedgerApi.V3.Data.MintValue qualified as MintValue
import PlutusLedgerApi.V3.Data.Tx qualified as Tx
import PlutusLedgerApi.V3.EvaluationContext qualified as EvaluationContext
import PlutusLedgerApi.V3.ParamName qualified as ParamName
import PlutusTx.Ratio qualified as Ratio

{-| An alias to the Plutus ledger language this module exposes at runtime.
 MAYBE: Use CPP '__FILE__' + some TH to automate this. -}
thisLedgerLanguage :: Common.PlutusLedgerLanguage
thisLedgerLanguage = Common.PlutusV3

{-| The deserialization from a serialised script into a `ScriptForEvaluation`,
ready to be evaluated on-chain.
Called inside phase-1 validation (i.e., deserialisation error is a phase-1 error). -}
deserialiseScript
  :: forall m
   . Common.MonadError Common.ScriptDecodeError m
  => Common.MajorProtocolVersion
  -- ^ which major protocol version the script was submitted in.
  -> Common.SerialisedScript
  -- ^ the script to deserialise.
  -> m Common.ScriptForEvaluation
deserialiseScript = Common.deserialiseScript thisLedgerLanguage

{-| Evaluates a script, returning the minimum budget that the script would need
to evaluate successfully. This will take as long as the script takes, if you need to
limit the execution time of the script also, you can use 'evaluateScriptRestricting', which
also returns the used budget. -}
evaluateScriptCounting
  :: Common.MajorProtocolVersion
  -- ^ Which protocol version to run the operation in
  -> Common.VerboseMode
  -- ^ Whether to produce log output
  -> EvaluationContext.EvaluationContext
  -- ^ Includes the cost model to use for tallying up the execution costs
  -> Common.ScriptForEvaluation
  -- ^ The script to evaluate
  -> Common.Data
  -- ^ The @ScriptContext@ argument to the script
  -> (Common.LogOutput, Either Common.EvaluationError Common.ExBudget)
evaluateScriptCounting mpv verbose ec s arg =
  Common.evaluateScriptCounting thisLedgerLanguage mpv verbose ec s [arg]

{-| Evaluates a script, with a cost model and a budget that restricts how many
resources it can use according to the cost model. Also returns the budget that
was actually used.

Can be used to calculate budgets for scripts, but even in this case you must give
a limit to guard against scripts that run for a long time or loop. -}
evaluateScriptRestricting
  :: Common.MajorProtocolVersion
  -- ^ Which protocol version to run the operation in
  -> Common.VerboseMode
  -- ^ Whether to produce log output
  -> EvaluationContext.EvaluationContext
  -- ^ Includes the cost model to use for tallying up the execution costs
  -> Common.ExBudget
  -- ^ The resource budget which must not be exceeded during evaluation
  -> Common.ScriptForEvaluation
  -- ^ The script to evaluate
  -> Common.Data
  -- ^ The @ScriptContext@ argument to the script
  -> (Common.LogOutput, Either Common.EvaluationError Common.ExBudget)
evaluateScriptRestricting mpv verbose ec budget s arg =
  Common.evaluateScriptRestricting thisLedgerLanguage mpv verbose ec budget s [arg]
