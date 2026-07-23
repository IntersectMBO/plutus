{-# LANGUAGE PatternSynonyms #-}

-- | The data-backed type interface to Plutus V4 for the ledger.
module PlutusLedgerApi.Data.V4
  ( -- * Accounts
    Contexts.AccountId (..)
  , Contexts.AccountBalanceInterval
  , pattern Contexts.AccountBalanceLowerBound
  , pattern Contexts.AccountBalanceUpperBound
  , pattern Contexts.AccountBalanceBothBounds
  , pattern Contexts.AccountBalanceExact
  , Contexts.AccountBalanceIntervals (..)

    -- * Governance
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
  , pattern Contexts.TxCertRegAccount
  , pattern Contexts.TxCertUnRegAccount
  , pattern Contexts.TxCertDelegAccount
  , pattern Contexts.TxCertRegAccountDeleg
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
  , pattern Contexts.GovernanceActionId
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

    -- * Context types
  , Contexts.ScriptContext
  , pattern Contexts.ScriptContext
  , Contexts.scriptContextTxInfo
  , Contexts.scriptContextRedeemer
  , Contexts.scriptContextScriptInfo
  , Contexts.scriptContextScriptHash
  , Contexts.ScriptPurpose
  , pattern Contexts.Minting
  , pattern Contexts.Spending
  , pattern Contexts.Withdrawing
  , pattern Contexts.Certifying
  , pattern Contexts.Voting
  , pattern Contexts.Proposing
  , pattern Contexts.Guarding
  , Contexts.ScriptInfo
  , pattern Contexts.MintingScript
  , pattern Contexts.SpendingScript
  , pattern Contexts.WithdrawingScript
  , pattern Contexts.CertifyingScript
  , pattern Contexts.VotingScript
  , pattern Contexts.ProposingScript
  , pattern Contexts.GuardingScript
  , Contexts.TopTxInfo
  , pattern Contexts.TopTxInfo
  , Contexts.topTxInfoSubTransactions
  , Contexts.topTxInfoDatums
  , Contexts.topTxInfoStartingBalanceIntervals
  , Contexts.topTxInfoSimplified
  , Contexts.TopTxInfoSimplified
  , pattern Contexts.TopTxInfoSimplified
  , Contexts.ttisIds
  , Contexts.ttisInputs
  , Contexts.ttisReferenceInputs
  , Contexts.ttisOutputs
  , Contexts.ttisMints
  , Contexts.ttisBurns
  , Contexts.ttisTxCerts
  , Contexts.ttisWithdrawals
  , Contexts.ttisDirectDeposits
  , Contexts.ttisValidRange
  , Contexts.ttisGuards
  , Contexts.ttisScriptPurposes
  , Contexts.ttisData
  , Contexts.ttisVotes
  , Contexts.ttisProposalProcedures
  , Contexts.ttisCurrentTreasuryAmount
  , Contexts.ttisTreasuryDonations

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
  , V2.AssetClass (..)
  , V2.assetClass
  , V2.assetClassValue
  , V2.assetClassValueOf
  , V2.currencySymbol
  , V2.currencySymbolValueOf
  , V2.flattenValue
  , V2.geq
  , V2.gt
  , V2.isZero
  , V2.leq
  , V2.lovelaceValue
  , V2.lovelaceValueOf
  , V2.lt
  , V2.scale
  , V2.split
  , V2.symbols
  , V2.tokenName
  , V2.unsafeLovelaceValueOf
  , V2.valueOf
  , V2.withCurrencySymbol

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
  , Contexts.txInfoId
  , Contexts.txInfoSubTxIx
  , Contexts.txInfoInputs
  , Contexts.txInfoReferenceInputs
  , Contexts.txInfoOutputs
  , Contexts.txInfoFee
  , Contexts.txInfoMint
  , Contexts.txInfoTxCerts
  , Contexts.txInfoWithdrawals
  , Contexts.txInfoDirectDeposits
  , Contexts.txInfoAccountBalanceIntervals
  , Contexts.txInfoValidRange
  , Contexts.txInfoGuards
  , Contexts.txInfoRequiredTopLevelGuards
  , Contexts.txInfoRedeemers
  , Contexts.txInfoData
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
  , V2.inclusiveLowerBound
  , V2.inclusiveUpperBound

    -- *** Ratio
  , Ratio.Rational
  , Ratio.ratio
  , Ratio.unsafeRatio
  , Ratio.numerator
  , Ratio.denominator
  , Ratio.fromHaskellRatio
  , Ratio.toHaskellRatio
  , Ratio.fromGHC
  , Ratio.toGHC

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
  ) where

import PlutusLedgerApi.Common qualified as Common
import PlutusLedgerApi.Data.V2 qualified as V2
import PlutusLedgerApi.V3.Data.MintValue qualified as MintValue
import PlutusLedgerApi.V3.Data.Tx qualified as Tx
import PlutusLedgerApi.V4.Data.Contexts qualified as Contexts
import PlutusTx.Ratio qualified as Ratio
