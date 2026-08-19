{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}

module PlutusLedgerApi.V4.Data.Contexts
  ( ColdCommitteeCredential (..)
  , HotCommitteeCredential (..)
  , DRepCredential (..)
  , DRep
  , matchDRep
  , pattern DRep
  , pattern DRepAlwaysAbstain
  , pattern DRepAlwaysNoConfidence
  , Delegatee
  , matchDelegatee
  , pattern DelegStake
  , pattern DelegVote
  , pattern DelegStakeVote
  , AccountId (..)
  , AccountBalanceInterval
  , matchAccountBalanceInterval
  , pattern AccountBalanceLowerBound
  , pattern AccountBalanceUpperBound
  , pattern AccountBalanceBothBounds
  , pattern AccountBalanceExact
  , AccountBalanceIntervals (..)
  , TxCert
  , matchTxCert
  , pattern TxCertRegAccount
  , pattern TxCertUnRegAccount
  , pattern TxCertDelegAccount
  , pattern TxCertRegAccountDeleg
  , pattern TxCertRegDRep
  , pattern TxCertUpdateDRep
  , pattern TxCertUnRegDRep
  , pattern TxCertPoolRegister
  , pattern TxCertPoolRetire
  , pattern TxCertAuthHotCommittee
  , pattern TxCertResignColdCommittee
  , Voter
  , matchVoter
  , pattern CommitteeVoter
  , pattern DRepVoter
  , pattern StakePoolVoter
  , Vote
  , matchVote
  , pattern VoteNo
  , pattern VoteYes
  , pattern Abstain
  , GovernanceActionId
  , pattern GovernanceActionId
  , matchGovernanceActionId
  , gaidTxId
  , gaidGovActionIx
  , Committee
  , pattern Committee
  , matchCommittee
  , committeeMembers
  , committeeQuorum
  , Constitution (..)
  , ProtocolVersion
  , pattern ProtocolVersion
  , matchProtocolVersion
  , pvMajor
  , pvMinor
  , ChangedParameters (..)
  , GovernanceAction
  , matchGovernanceAction
  , pattern ParameterChange
  , pattern HardForkInitiation
  , pattern TreasuryWithdrawals
  , pattern NoConfidence
  , pattern UpdateCommittee
  , pattern NewConstitution
  , pattern InfoAction
  , ProposalProcedure
  , pattern ProposalProcedure
  , matchProposalProcedure
  , ppDeposit
  , ppReturnAddr
  , ppGovernanceAction
  , ScriptPurpose
  , matchScriptPurpose
  , pattern Minting
  , pattern Spending
  , pattern Withdrawing
  , pattern Certifying
  , pattern Voting
  , pattern Proposing
  , pattern Guarding
  , TxInInfo
  , pattern TxInInfo
  , matchTxInInfo
  , txInInfoOutRef
  , txInInfoResolved
  , TxInfo
  , pattern TxInfo
  , matchTxInfo
  , txInfoId
  , txInfoSubTxIx
  , txInfoInputs
  , txInfoReferenceInputs
  , txInfoOutputs
  , txInfoMint
  , txInfoTxCerts
  , txInfoWithdrawals
  , txInfoDirectDeposits
  , txInfoAccountBalanceIntervals
  , txInfoValidRange
  , txInfoGuards
  , txInfoRequiredTopLevelGuards
  , txInfoRedeemers
  , txInfoData
  , txInfoVotes
  , txInfoProposalProcedures
  , txInfoCurrentTreasuryAmount
  , txInfoTreasuryDonation
  , TopTxInfoSimplified
  , pattern TopTxInfoSimplified
  , matchTopTxInfoSimplified
  , ttisIds
  , ttisInputs
  , ttisReferenceInputs
  , ttisOutputs
  , ttisMints
  , ttisBurns
  , ttisTxCerts
  , ttisWithdrawals
  , ttisDirectDeposits
  , ttisValidRange
  , ttisGuards
  , ttisRequiredTopLevelGuards
  , ttisScriptPurposes
  , ttisData
  , ttisVotes
  , ttisProposalProcedures
  , ttisCurrentTreasuryAmount
  , ttisTreasuryDonations
  , TopTxInfo
  , pattern TopTxInfo
  , matchTopTxInfo
  , topTxInfoSubTransactions
  , topTxInfoDatums
  , topTxInfoStartingAccountBalanceIntervals
  , topTxInfoSimplified
  , ScriptInfo
  , matchScriptInfo
  , pattern MintingScript
  , pattern SpendingScript
  , pattern WithdrawingScript
  , pattern CertifyingScript
  , pattern VotingScript
  , pattern ProposingScript
  , pattern GuardingScript
  , ScriptContext
  , pattern ScriptContext
  , matchScriptContext
  , scriptContextTxInfo
  , scriptContextRedeemer
  , scriptContextScriptInfo
  , scriptContextScriptHash
  , findOwnInput
  , findDatum
  , findDatumHash
  , findTxInByTxOutRef
  , findContinuingOutputs
  , getContinuingOutputs
  , txSignedBy
  , pubKeyOutputsAt
  , valuePaidTo
  , valueSpent
  , valueProduced
  , ownCurrencySymbol
  , spendsOutput
  ) where

import GHC.Generics (Generic)
import Prettyprinter (nest, vsep, (<+>))
import Prettyprinter.Extras

import PlutusLedgerApi.Data.V2 qualified as V2
import PlutusLedgerApi.V3.Data.Contexts
  ( ChangedParameters (..)
  , ColdCommitteeCredential (..)
  , Committee
  , Constitution (..)
  , DRep
  , DRepCredential (..)
  , Delegatee
  , GovernanceAction
  , GovernanceActionId
  , HotCommitteeCredential (..)
  , ProposalProcedure
  , ProtocolVersion
  , Vote
  , Voter
  , committeeMembers
  , committeeQuorum
  , gaidGovActionIx
  , gaidTxId
  , matchCommittee
  , matchDRep
  , matchDelegatee
  , matchGovernanceAction
  , matchGovernanceActionId
  , matchProposalProcedure
  , matchProtocolVersion
  , matchVote
  , matchVoter
  , ppDeposit
  , ppGovernanceAction
  , ppReturnAddr
  , pvMajor
  , pvMinor
  , pattern Abstain
  , pattern Committee
  , pattern CommitteeVoter
  , pattern DRep
  , pattern DRepAlwaysAbstain
  , pattern DRepAlwaysNoConfidence
  , pattern DRepVoter
  , pattern DelegStake
  , pattern DelegStakeVote
  , pattern DelegVote
  , pattern GovernanceActionId
  , pattern HardForkInitiation
  , pattern InfoAction
  , pattern NewConstitution
  , pattern NoConfidence
  , pattern ParameterChange
  , pattern ProposalProcedure
  , pattern ProtocolVersion
  , pattern StakePoolVoter
  , pattern TreasuryWithdrawals
  , pattern UpdateCommittee
  , pattern VoteNo
  , pattern VoteYes
  )
import PlutusLedgerApi.V3.Data.MintValue qualified as V3
import PlutusLedgerApi.V3.Data.Tx qualified as V3
import PlutusLedgerApi.V4.Data.Address (AccountId (..), pattern Address)
import PlutusLedgerApi.V4.Data.Time (POSIXTimeRange)
import PlutusLedgerApi.V4.Data.Tx (TxOut, txOutAddress, txOutValue, pattern TxOut)
import PlutusTx qualified
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.BuiltinList qualified as BuiltinList
import PlutusTx.Builtins.Internal qualified as Builtins
import PlutusTx.Data.AssocMap
import PlutusTx.Data.List (List)
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.Prelude qualified as PlutusTx

import Prelude qualified as Haskell

PlutusTx.asData
  [d|
    data AccountBalanceInterval
      = AccountBalanceLowerBound V2.Lovelace
      | AccountBalanceUpperBound V2.Lovelace
      | AccountBalanceBothBounds V2.Lovelace V2.Lovelace
      | AccountBalanceExact V2.Lovelace
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow AccountBalanceInterval)
    |]

PlutusTx.deriveEq ''AccountBalanceInterval
PlutusTx.makeLift ''AccountBalanceInterval

newtype AccountBalanceIntervals
  = AccountBalanceIntervals (Map AccountId AccountBalanceInterval)
  deriving stock (Generic)
  deriving (Pretty) via (PrettyShow AccountBalanceIntervals)
  deriving newtype
    ( Haskell.Show
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )

PlutusTx.makeLift ''AccountBalanceIntervals

PlutusTx.asData
  [d|
    data TxCert
      = TxCertRegAccount AccountId V2.Lovelace
      | TxCertUnRegAccount AccountId V2.Lovelace
      | TxCertDelegAccount AccountId Delegatee
      | TxCertRegAccountDeleg AccountId Delegatee V2.Lovelace
      | TxCertRegDRep DRepCredential V2.Lovelace
      | TxCertUpdateDRep DRepCredential
      | TxCertUnRegDRep DRepCredential V2.Lovelace
      | TxCertPoolRegister V2.PubKeyHash V2.PubKeyHash
      | TxCertPoolRetire V2.PubKeyHash Haskell.Integer
      | TxCertAuthHotCommittee ColdCommitteeCredential HotCommitteeCredential
      | TxCertResignColdCommittee ColdCommitteeCredential
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow TxCert)
    |]

PlutusTx.deriveEq ''TxCert
PlutusTx.makeLift ''TxCert

PlutusTx.asData
  [d|
    data ScriptPurpose
      = Minting V2.ScriptHash V2.CurrencySymbol
      | Spending V2.ScriptHash V3.TxOutRef
      | Withdrawing V2.ScriptHash V2.Credential
      | Certifying V2.ScriptHash Haskell.Integer TxCert
      | Voting V2.ScriptHash Voter
      | Proposing V2.ScriptHash Haskell.Integer ProposalProcedure
      | Guarding V2.ScriptHash Haskell.Integer
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow ScriptPurpose)
    |]

PlutusTx.makeLift ''ScriptPurpose

PlutusTx.asData
  [d|
    data TxInInfo = TxInInfo
      { txInInfoOutRef :: V3.TxOutRef
      , txInInfoResolved :: TxOut
      }
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.deriveEq ''TxInInfo
PlutusTx.makeLift ''TxInInfo

instance Pretty TxInInfo where
  pretty TxInInfo {txInInfoOutRef, txInInfoResolved} =
    pretty txInInfoOutRef <+> "->" <+> pretty txInInfoResolved

PlutusTx.asData
  [d|
    data TxInfo = TxInfo
      { txInfoId :: V3.TxId
      , txInfoSubTxIx :: Haskell.Maybe Haskell.Integer
      , txInfoInputs :: List TxInInfo
      , txInfoReferenceInputs :: List TxInInfo
      , txInfoOutputs :: List TxOut
      , txInfoMint :: V3.MintValue
      , txInfoTxCerts :: List TxCert
      , txInfoWithdrawals :: Map V2.Credential V2.Lovelace
      , txInfoDirectDeposits :: Map V2.Credential V2.Lovelace
      , txInfoAccountBalanceIntervals :: AccountBalanceIntervals
      , txInfoValidRange :: POSIXTimeRange
      , txInfoGuards :: List V2.Credential
      , txInfoRequiredTopLevelGuards :: Map V2.Credential (Haskell.Maybe V2.Datum)
      , txInfoRedeemers :: Map ScriptPurpose V2.Redeemer
      , txInfoData :: Map V2.DatumHash V2.Datum
      , txInfoVotes :: Map Voter (Map GovernanceActionId Vote)
      , txInfoProposalProcedures :: List ProposalProcedure
      , txInfoCurrentTreasuryAmount :: Haskell.Maybe V2.Lovelace
      , txInfoTreasuryDonation :: V2.Lovelace
      }
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.makeLift ''TxInfo

PlutusTx.asData
  [d|
    data TopTxInfoSimplified = TopTxInfoSimplified
      { ttisIds :: List V3.TxId
      , -- \^ List of all `TxId`s fro the whole transaction, including the top-level transaction,
        -- which is always going to be the last one in the list.
        ttisInputs :: List TxInInfo
      , -- \^ Concatenated list of all `txInfoInputs`'
        ttisReferenceInputs :: List TxInInfo
      , -- \^ Concatenated list of all `txInfoReferenceInputs`'
        ttisOutputs :: List TxOut
      , -- \^ Concatenated list of all `txInfoOutputs`'
        ttisMints :: V3.MintValue
      , -- \^ `MintValue`s from all `txInfoMint` with positive amounts
        ttisBurns :: V3.MintValue
      , -- \^ `MintValue`s from all `txInfoMint` with negative amounts
        ttisTxCerts :: List TxCert
      , -- \^ Concatenated list of all `ttisTxCerts`'. Note, that unlike individual lists in each
        -- `txInfoTxCerts`, this one can contain duplicates.
        ttisWithdrawals :: Map V2.Credential V2.Lovelace
      , -- \^ Union of all `txInfoWithdrawals` with a sum on the range for duplicate credentials
        ttisDirectDeposits :: Map V2.Credential V2.Lovelace
      , -- \^ Union of all `txInfoWithdrawals` with a sum on the range for duplicate credentials
        ttisValidRange :: POSIXTimeRange
      , -- \^ Intersection of all validity intervals from within the whole transaction
        ttisGuards :: List V2.Credential
      , -- \^ Concatenated list of all `txInfoGuards`'
        ttisRequiredTopLevelGuards :: List V2.Credential
      , -- \^ Deduplicated set of required top level guards. It is impossible to keep the range of
        -- the Map due to potential presence of duplicates in the domain between different
        -- sub-transactions, therefore the range is eliminated.
        ttisScriptPurposes :: List ScriptPurpose
      , -- \^ Union of all of the `Redeemer`s. Note that it is not possible to preserve actual
        -- `Redeemer`s upon `union` operation due to potential duplicates in the domain. Therefore it
        -- is collapsed to a Set of `ScriptPurpose`s only with duplicates removed.
        ttisData :: Map V2.DatumHash V2.Datum
      , -- \^ Union of all `txInfoData`. Duplicates are simply removed, since domain and range are
        -- a one-to-one mapping.
        ttisVotes :: Map Voter (Map GovernanceActionId Vote)
      , -- \^ Union of all of the votes. Note that a vote in a sub-sequent sub-transaction or a top
        -- level transaction can replace a vote from a prior sub-transaction.
        ttisProposalProcedures :: List ProposalProcedure
      , -- \^ Concatenated list of all `ProposalPrecedure`s.
        ttisCurrentTreasuryAmount :: Haskell.Maybe V2.Lovelace
      , -- \^ Value of the treasury, which will be present if any of sub-transactions or top level
        -- transaction included such value
        ttisTreasuryDonations :: V2.Lovelace
        -- \^ Sum of all `txInfoTreasuryDonation`s
      }
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow TopTxInfoSimplified)
    |]

PlutusTx.makeLift ''TopTxInfoSimplified

PlutusTx.asData
  [d|
    data TopTxInfo = TopTxInfo
      { topTxInfoSubTransactions :: List TxInfo
      , -- \^ List of `TxInfo`s for all sub-transactions. Not that `TxInfo` for the top level
        -- transaction itslef is not present in this list.
        topTxInfoDatums :: Map V3.TxId V2.Datum
      , -- \^ Datums supplied in `requiredTopLevelGuards` for that script. Plutus scripts require
        -- a datum to be supplied when listed `requiredTopLevelGuards`. That `Map` will be empty if
        -- none of the transactions within the whole transaction require Plutus scripts to be
        -- present in `Guards`
        topTxInfoStartingAccountBalanceIntervals :: AccountBalanceIntervals
      , -- \^ This is a field that allows top level transaction to specify the balance intervals
        -- before the whole transaction is applied
        topTxInfoSimplified :: TopTxInfoSimplified
        -- \^ Aggregated view on the whole transaction, namely information about sub-transactions
        -- and the top level transaction all concatenated together with loss of some information
      }
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow TopTxInfo)
    |]

PlutusTx.makeLift ''TopTxInfo

PlutusTx.asData
  [d|
    data ScriptInfo
      = MintingScript V2.CurrencySymbol
      | SpendingScript V3.TxOutRef (Haskell.Maybe V2.Datum)
      | WithdrawingScript AccountId
      | CertifyingScript
          Haskell.Integer
          -- \^ 0-based index of the given `TxCert` in `txInfoTxCerts`
          TxCert
      | VotingScript Voter
      | ProposingScript
          Haskell.Integer
          -- \^ 0-based index of the given `ProposalProcedure` in `txInfoProposalProcedures`
          ProposalProcedure
      | GuardingScript
          Haskell.Integer
          (Haskell.Maybe TopTxInfo)
      -- \^ Whenever a `Guard` is executed at the top transaction level it will include extra
      -- information about potential sub-transactions. In other words for sub-transactions
      -- this is guaranteed to be `Nothing`, while for top level transactions this is
      -- guaranteed to be `Just`
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow ScriptInfo)
    |]

PlutusTx.makeLift ''ScriptInfo

PlutusTx.asData
  [d|
    data ScriptContext = ScriptContext
      { scriptContextTxInfo :: TxInfo
      , -- \^ Information about the transaction the currently-executing script is included in
        scriptContextRedeemer :: V2.Redeemer
      , -- \^ Redeemer for the currently-executing script
        scriptContextScriptInfo :: ScriptInfo
      , -- \^ the purpose of the currently-executing script, along with information associated
        -- with the purpose
        scriptContextScriptHash :: V2.ScriptHash
        -- \^ Hash of the script that is being executed
      }
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.makeLift ''ScriptContext

{-# INLINEABLE findOwnInput #-}
findOwnInput :: ScriptContext -> Haskell.Maybe TxInInfo
findOwnInput
  ScriptContext
    { scriptContextTxInfo = TxInfo {txInfoInputs}
    , scriptContextScriptInfo = SpendingScript txOutRef _
    } =
    Data.List.find
      (\TxInInfo {txInInfoOutRef} -> txInInfoOutRef PlutusTx.== txOutRef)
      txInfoInputs
findOwnInput _ = Haskell.Nothing

{-# INLINEABLE findDatum #-}
findDatum :: V2.DatumHash -> TxInfo -> Haskell.Maybe V2.Datum
findDatum dsh TxInfo {txInfoData} = lookup dsh txInfoData

{-# INLINEABLE findDatumHash #-}
findDatumHash :: V2.Datum -> TxInfo -> Haskell.Maybe V2.DatumHash
findDatumHash ds TxInfo {txInfoData} =
  getHash PlutusTx.<$> BuiltinList.find matchDatum (toBuiltinList txInfoData)
  where
    getHash = PlutusTx.unsafeFromBuiltinData PlutusTx.. Builtins.fst
    matchDatum pair = Builtins.snd pair PlutusTx.== V2.getDatum ds

{-# INLINEABLE findTxInByTxOutRef #-}
findTxInByTxOutRef :: V3.TxOutRef -> TxInfo -> Haskell.Maybe TxInInfo
findTxInByTxOutRef outRef TxInfo {txInfoInputs} =
  Data.List.find
    (\TxInInfo {txInInfoOutRef} -> txInInfoOutRef PlutusTx.== outRef)
    txInfoInputs

{-# INLINEABLE findContinuingOutputs #-}

{-| Find the indices of outputs in the current sub-transaction or top-level transaction
that pay to the same script address we are currently spending from. This does not search
the outputs of the whole transaction. -}
findContinuingOutputs :: ScriptContext -> List Haskell.Integer
findContinuingOutputs ctx
  | Haskell.Just TxInInfo {txInInfoResolved = TxOut {txOutAddress}} <- findOwnInput ctx =
      Data.List.findIndices
        (f txOutAddress)
        (txInfoOutputs (scriptContextTxInfo ctx))
  where
    f addr TxOut {txOutAddress = otherAddress} = addr PlutusTx.== otherAddress
findContinuingOutputs _ = PlutusTx.traceError "Le"

{-# INLINEABLE getContinuingOutputs #-}

{-| Get the outputs in the current sub-transaction or top-level transaction that pay to
the same script address we are currently spending from. This does not search the outputs
of the whole transaction. -}
getContinuingOutputs :: ScriptContext -> List TxOut
getContinuingOutputs ctx
  | Haskell.Just TxInInfo {txInInfoResolved = TxOut {txOutAddress}} <- findOwnInput ctx =
      Data.List.filter (f txOutAddress) (txInfoOutputs (scriptContextTxInfo ctx))
  where
    f addr TxOut {txOutAddress = otherAddress} = addr PlutusTx.== otherAddress
getContinuingOutputs _ = PlutusTx.traceError "Lf"

{-# INLINEABLE txSignedBy #-}
txSignedBy :: TxInfo -> V2.PubKeyHash -> Haskell.Bool
txSignedBy TxInfo {txInfoGuards} keyHash =
  case Data.List.find isSigner txInfoGuards of
    Haskell.Just _ -> Haskell.True
    Haskell.Nothing -> Haskell.False
  where
    isSigner (V2.PubKeyCredential guardKeyHash) = guardKeyHash PlutusTx.== keyHash
    isSigner _ = Haskell.False

{-# INLINEABLE pubKeyOutputsAt #-}
pubKeyOutputsAt :: V2.PubKeyHash -> TxInfo -> List V2.Value
pubKeyOutputsAt pk p =
  let flt TxOut {txOutAddress = Address (V2.PubKeyCredential pk') _, txOutValue}
        | pk PlutusTx.== pk' = Haskell.Just txOutValue
      flt _ = Haskell.Nothing
   in Data.List.mapMaybe flt (txInfoOutputs p)

{-# INLINEABLE valuePaidTo #-}
valuePaidTo :: TxInfo -> V2.PubKeyHash -> V2.Value
valuePaidTo ptx pkh = Data.List.mconcat (pubKeyOutputsAt pkh ptx)

{-# INLINEABLE valueSpent #-}
valueSpent :: TxInfo -> V2.Value
valueSpent = Data.List.foldMap (txOutValue PlutusTx.. txInInfoResolved) PlutusTx.. txInfoInputs

{-# INLINEABLE valueProduced #-}
valueProduced :: TxInfo -> V2.Value
valueProduced = Data.List.foldMap txOutValue PlutusTx.. txInfoOutputs

{-# INLINEABLE ownCurrencySymbol #-}
ownCurrencySymbol :: ScriptContext -> V2.CurrencySymbol
ownCurrencySymbol ScriptContext {scriptContextScriptInfo = MintingScript cs} = cs
ownCurrencySymbol _ = PlutusTx.traceError "Lh"

{-# INLINEABLE spendsOutput #-}
spendsOutput :: TxInfo -> V3.TxId -> Haskell.Integer -> Haskell.Bool
spendsOutput txInfo txId i =
  let spendsOutRef inp =
        let outRef = txInInfoOutRef inp
         in txId
              PlutusTx.== V3.txOutRefId outRef
              PlutusTx.&& i
              PlutusTx.== V3.txOutRefIdx outRef
   in Data.List.any spendsOutRef (txInfoInputs txInfo)

instance Pretty TxInfo where
  pretty TxInfo {..} =
    vsep
      [ "TxId:" <+> pretty txInfoId
      , "Sub-transaction index:" <+> pretty txInfoSubTxIx
      , "Inputs:" <+> pretty txInfoInputs
      , "Reference inputs:" <+> pretty txInfoReferenceInputs
      , "Outputs:" <+> pretty txInfoOutputs
      , "Value minted:" <+> pretty txInfoMint
      , "TxCerts:" <+> pretty txInfoTxCerts
      , "Withdrawals:" <+> pretty txInfoWithdrawals
      , "Direct deposits:" <+> pretty txInfoDirectDeposits
      , "Account balance intervals:" <+> pretty txInfoAccountBalanceIntervals
      , "Valid range:" <+> pretty txInfoValidRange
      , "Guards:" <+> pretty txInfoGuards
      , "Required top-level guards:" <+> pretty txInfoRequiredTopLevelGuards
      , "Redeemers:" <+> pretty txInfoRedeemers
      , "Datums:" <+> pretty txInfoData
      , "Votes:" <+> pretty txInfoVotes
      , "Proposal procedures:" <+> pretty txInfoProposalProcedures
      , "Current treasury amount:" <+> pretty txInfoCurrentTreasuryAmount
      , "Treasury donation:" <+> pretty txInfoTreasuryDonation
      ]

instance Pretty ScriptContext where
  pretty ScriptContext {..} =
    vsep
      [ "ScriptInfo:" <+> pretty scriptContextScriptInfo
      , "ScriptHash:" <+> pretty scriptContextScriptHash
      , nest 2 (vsep ["TxInfo:", pretty scriptContextTxInfo])
      , nest 2 (vsep ["Redeemer:", pretty scriptContextRedeemer])
      ]
