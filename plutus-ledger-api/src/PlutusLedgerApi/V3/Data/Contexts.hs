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
-- needed for asData pattern synonyms
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}

module PlutusLedgerApi.V3.Data.Contexts
  ( ColdCommitteeCredential (..)
  , HotCommitteeCredential (..)
  , DRepCredential (..)
  , DRep
  , pattern DRep
  , pattern DRepAlwaysAbstain
  , pattern DRepAlwaysNoConfidence
  , Delegatee
  , pattern DelegStake
  , pattern DelegVote
  , pattern DelegStakeVote
  , TxCert
  , pattern TxCertRegStaking
  , pattern TxCertUnRegStaking
  , pattern TxCertDelegStaking
  , pattern TxCertRegDeleg
  , pattern TxCertRegDRep
  , pattern TxCertUpdateDRep
  , pattern TxCertUnRegDRep
  , pattern TxCertPoolRegister
  , pattern TxCertPoolRetire
  , pattern TxCertAuthHotCommittee
  , pattern TxCertResignColdCommittee
  , Voter
  , pattern CommitteeVoter
  , pattern DRepVoter
  , pattern StakePoolVoter
  , Vote
  , pattern VoteNo
  , pattern VoteYes
  , pattern Abstain
  , GovernanceActionId
  , pattern GovernanceActionId
  , gaidTxId
  , gaidGovActionIx
  , Committee
  , pattern Committee
  , committeeMembers
  , committeeQuorum
  , Constitution (..)
  , ProtocolVersion
  , pattern ProtocolVersion
  , pvMajor
  , pvMinor
  , ChangedParameters (..)
  , GovernanceAction
  , pattern ParameterChange
  , pattern HardForkInitiation
  , pattern TreasuryWithdrawals
  , pattern NoConfidence
  , pattern UpdateCommittee
  , pattern NewConstitution
  , pattern InfoAction
  , ProposalProcedure
  , pattern ProposalProcedure
  , ppDeposit
  , ppReturnAddr
  , ppGovernanceAction
  , ScriptPurpose
  , pattern Minting
  , pattern Spending
  , pattern Rewarding
  , pattern Certifying
  , pattern Voting
  , pattern Proposing
  , ScriptInfo
  , pattern MintingScript
  , pattern SpendingScript
  , pattern RewardingScript
  , pattern CertifyingScript
  , pattern VotingScript
  , pattern ProposingScript
  , TxInInfo
  , pattern TxInInfo
  , txInInfoOutRef
  , txInInfoResolved
  , TxInfo
  , pattern TxInfo
  , txInfoInputs
  , txInfoReferenceInputs
  , txInfoOutputs
  , txInfoFee
  , txInfoMint
  , txInfoTxCerts
  , txInfoWdrl
  , txInfoValidRange
  , txInfoSignatories
  , txInfoRedeemers
  , txInfoData
  , txInfoId
  , txInfoVotes
  , txInfoProposalProcedures
  , txInfoCurrentTreasuryAmount
  , txInfoTreasuryDonation
  , ScriptContext
  , pattern ScriptContext
  , scriptContextTxInfo
  , scriptContextRedeemer
  , scriptContextScriptInfo
  , findOwnInput
  , findDatum
  , findDatumHash
  , findTxInByTxOutRef
  , findContinuingOutputs
  , getContinuingOutputs
  , txSignedBy

    -- * Validator functions
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
import PlutusLedgerApi.V3.Data.MintValue qualified as V3
import PlutusLedgerApi.V3.Data.Tx qualified as V3
import PlutusTx qualified
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Data.AssocMap
import PlutusTx.Data.List (List)
import PlutusTx.Data.List qualified as Data.List
import PlutusTx.List qualified as List
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Ratio (Rational)

import Prelude qualified as Haskell

newtype ColdCommitteeCredential = ColdCommitteeCredential V2.Credential
  deriving stock (Generic)
  deriving (Pretty) via (PrettyShow ColdCommitteeCredential)
  deriving newtype
    ( Haskell.Eq
    , Haskell.Show
    , PlutusTx.Eq
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )

PlutusTx.makeLift ''ColdCommitteeCredential

newtype HotCommitteeCredential = HotCommitteeCredential V2.Credential
  deriving stock (Generic)
  deriving (Pretty) via (PrettyShow HotCommitteeCredential)
  deriving newtype
    ( Haskell.Eq
    , Haskell.Show
    , PlutusTx.Eq
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )

PlutusTx.makeLift ''HotCommitteeCredential

newtype DRepCredential = DRepCredential V2.Credential
  deriving stock (Generic)
  deriving (Pretty) via (PrettyShow DRepCredential)
  deriving newtype
    ( Haskell.Eq
    , Haskell.Show
    , PlutusTx.Eq
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )

PlutusTx.makeLift ''DRepCredential

PlutusTx.asData
  [d|
    data DRep
      = DRep DRepCredential
      | DRepAlwaysAbstain
      | DRepAlwaysNoConfidence
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow DRep)
    |]

PlutusTx.deriveEq ''DRep
PlutusTx.makeLift ''DRep

PlutusTx.asData
  [d|
    data Delegatee
      = DelegStake V2.PubKeyHash
      | DelegVote DRep
      | DelegStakeVote V2.PubKeyHash DRep
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow Delegatee)
    |]

PlutusTx.deriveEq ''Delegatee
PlutusTx.makeLift ''Delegatee

PlutusTx.asData
  [d|
    data TxCert
      = -- \| Register staking credential with an optional deposit amount
        TxCertRegStaking V2.Credential (Haskell.Maybe V2.Lovelace)
      | -- \| Un-Register staking credential with an optional refund amount
        TxCertUnRegStaking V2.Credential (Haskell.Maybe V2.Lovelace)
      | -- \| Delegate staking credential to a Delegatee
        TxCertDelegStaking V2.Credential Delegatee
      | -- \| Register and delegate staking credential to a Delegatee in one certificate. Noter that
        -- deposit is mandatory.
        TxCertRegDeleg V2.Credential Delegatee V2.Lovelace
      | -- \| Register a DRep with a deposit value. The optional anchor is omitted.
        TxCertRegDRep DRepCredential V2.Lovelace
      | -- \| Update a DRep. The optional anchor is omitted.
        TxCertUpdateDRep DRepCredential
      | -- \| UnRegister a DRep with mandatory refund value
        TxCertUnRegDRep DRepCredential V2.Lovelace
      | -- \| A digest of the PoolParams
        TxCertPoolRegister
          V2.PubKeyHash
          -- \^ poolId
          V2.PubKeyHash
      | -- \^ pool VFR
        -- \| The retirement certificate and the Epoch in which the retirement will take place
        TxCertPoolRetire V2.PubKeyHash Haskell.Integer
      | -- \| Authorize a Hot credential for a specific Committee member's cold credential
        TxCertAuthHotCommittee ColdCommitteeCredential HotCommitteeCredential
      | TxCertResignColdCommittee ColdCommitteeCredential
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow TxCert)
    |]

PlutusTx.deriveEq ''TxCert
PlutusTx.makeLift ''TxCert

PlutusTx.asData
  [d|
    data Voter
      = CommitteeVoter HotCommitteeCredential
      | DRepVoter DRepCredential
      | StakePoolVoter V2.PubKeyHash
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow Voter)
    |]

PlutusTx.deriveEq ''Voter
PlutusTx.makeLift ''Voter

-- | A vote. The optional anchor is omitted.
PlutusTx.asData
  [d|
    data Vote
      = VoteNo
      | VoteYes
      | Abstain
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow Vote)
    |]

PlutusTx.deriveEq ''Vote
PlutusTx.makeLift ''Vote

-- | Similar to TxOutRef, but for GovActions
PlutusTx.asData
  [d|
    data GovernanceActionId = GovernanceActionId
      { gaidTxId :: V3.TxId
      , gaidGovActionIx :: Haskell.Integer
      }
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.deriveEq ''GovernanceActionId
PlutusTx.makeLift ''GovernanceActionId

instance Pretty GovernanceActionId where
  pretty GovernanceActionId {..} =
    vsep
      [ "gaidTxId:" <+> pretty gaidTxId
      , "gaidGovActionIx:" <+> pretty gaidGovActionIx
      ]

PlutusTx.asData
  [d|
    data Committee = Committee
      { committeeMembers :: Map ColdCommitteeCredential Haskell.Integer
      , -- \^ Committee members with epoch number when each of them expires
        committeeQuorum :: PlutusTx.Rational
      }
      -- \^ Quorum of the committee that is necessary for a successful vote

      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.makeLift ''Committee

instance Pretty Committee where
  pretty Committee {..} =
    vsep
      [ "committeeMembers:" <+> pretty committeeMembers
      , "committeeQuorum:" <+> pretty committeeQuorum
      ]

-- | A constitution. The optional anchor is omitted.
newtype Constitution = Constitution
  { constitutionScript :: Haskell.Maybe V2.ScriptHash
  }
  deriving stock (Generic)
  deriving newtype (Haskell.Show, Haskell.Eq)

PlutusTx.deriveEq ''Constitution
PlutusTx.makeLift ''Constitution
PlutusTx.makeIsDataIndexed ''Constitution [('Constitution, 0)]

instance Pretty Constitution where
  pretty (Constitution script) = "constitutionScript:" <+> pretty script

PlutusTx.asData
  [d|
    data ProtocolVersion = ProtocolVersion
      { pvMajor :: Haskell.Integer
      , pvMinor :: Haskell.Integer
      }
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.deriveEq ''ProtocolVersion
PlutusTx.makeLift ''ProtocolVersion

instance Pretty ProtocolVersion where
  pretty ProtocolVersion {..} =
    vsep
      [ "pvMajor:" <+> pretty pvMajor
      , "pvMinor:" <+> pretty pvMinor
      ]

{-| A Plutus Data object containing proposed parameter changes. The Data object contains
a @Map@ with one entry per changed parameter, from the parameter ID to the new value.
Unchanged parameters are not included.

The mapping from parameter IDs to parameters can be found in
[conway.cddl](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl). -- editorconfig-checker-disable-file

/Invariant:/ This map is non-empty, and the keys are stored in ascending order. -}
newtype ChangedParameters = ChangedParameters {getChangedParameters :: PlutusTx.BuiltinData}
  deriving stock (Generic, Haskell.Show)
  deriving newtype
    ( Haskell.Eq
    , Haskell.Ord
    , PlutusTx.Eq
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    , Pretty
    )

PlutusTx.makeLift ''ChangedParameters

PlutusTx.asData
  [d|
    data GovernanceAction
      = ParameterChange
          (Haskell.Maybe GovernanceActionId)
          ChangedParameters
          (Haskell.Maybe V2.ScriptHash)
      | -- \^ Hash of the constitution script
        -- \| proposal to update protocol version
        HardForkInitiation (Haskell.Maybe GovernanceActionId) ProtocolVersion
      | TreasuryWithdrawals
          (Map V2.Credential V2.Lovelace)
          (Haskell.Maybe V2.ScriptHash)
      | -- \^ Hash of the constitution script
        NoConfidence (Haskell.Maybe GovernanceActionId)
      | UpdateCommittee
          (Haskell.Maybe GovernanceActionId)
          (List ColdCommitteeCredential)
          -- \^ Committee members to be removed
          (Map ColdCommitteeCredential Haskell.Integer)
          -- \^ Committee members to be added
          Rational
      | -- \^ New quorum
        NewConstitution (Haskell.Maybe GovernanceActionId) Constitution
      | InfoAction
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow GovernanceAction)
    |]

PlutusTx.makeLift ''GovernanceAction

-- | A proposal procedure. The optional anchor is omitted.
PlutusTx.asData
  [d|
    data ProposalProcedure = ProposalProcedure
      { ppDeposit :: V2.Lovelace
      , ppReturnAddr :: V2.Credential
      , ppGovernanceAction :: GovernanceAction
      }
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.makeLift ''ProposalProcedure

instance Pretty ProposalProcedure where
  pretty ProposalProcedure {..} =
    vsep
      [ "ppDeposit:" <+> pretty ppDeposit
      , "ppReturnAddr:" <+> pretty ppReturnAddr
      , "ppGovernanceAction:" <+> pretty ppGovernanceAction
      ]

-- | A `ScriptPurpose` uniquely identifies a Plutus script within a transaction.
PlutusTx.asData
  [d|
    data ScriptPurpose
      = Minting V2.CurrencySymbol
      | Spending V3.TxOutRef
      | Rewarding V2.Credential
      | Certifying
          Haskell.Integer
          -- \^ 0-based index of the given `TxCert` in `txInfoTxCerts`
          TxCert
      | Voting Voter
      | Proposing
          Haskell.Integer
          -- \^ 0-based index of the given `ProposalProcedure` in `txInfoProposalProcedures`
          ProposalProcedure
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow ScriptPurpose)
    |]

PlutusTx.makeLift ''ScriptPurpose

-- | Like `ScriptPurpose` but with an optional datum for spending scripts.
PlutusTx.asData
  [d|
    data ScriptInfo
      = MintingScript V2.CurrencySymbol
      | SpendingScript V3.TxOutRef (Haskell.Maybe V2.Datum)
      | RewardingScript V2.Credential
      | CertifyingScript
          Haskell.Integer
          -- \^ 0-based index of the given `TxCert` in `txInfoTxCerts`
          TxCert
      | VotingScript Voter
      | ProposingScript
          Haskell.Integer
          -- \^ 0-based index of the given `ProposalProcedure` in `txInfoProposalProcedures`
          ProposalProcedure
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow ScriptInfo)
    |]

PlutusTx.makeLift ''ScriptInfo

-- | An input of a pending transaction.
PlutusTx.asData
  [d|
    data TxInInfo = TxInInfo
      { txInInfoOutRef :: V3.TxOutRef
      , txInInfoResolved :: V2.TxOut
      }
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.deriveEq ''TxInInfo
PlutusTx.makeLift ''TxInInfo

instance Pretty TxInInfo where
  pretty TxInInfo {txInInfoOutRef, txInInfoResolved} =
    pretty txInInfoOutRef <+> "->" <+> pretty txInInfoResolved

-- | TxInfo for PlutusV3
PlutusTx.asData
  [d|
    data TxInfo = TxInfo
      { txInfoInputs :: List TxInInfo
      , txInfoReferenceInputs :: List TxInInfo
      , txInfoOutputs :: List V2.TxOut
      , txInfoFee :: V2.Lovelace
      , txInfoMint :: V3.MintValue
      , -- \^ The 'Value' minted by this transaction.
        --
        -- /Invariant:/ This field does not contain Ada with zero quantity, unlike
        -- their namesakes in Plutus V1 and V2's ScriptContexts.
        txInfoTxCerts :: List TxCert
      , txInfoWdrl :: Map V2.Credential V2.Lovelace
      , txInfoValidRange :: V2.POSIXTimeRange
      , txInfoSignatories :: List V2.PubKeyHash
      , txInfoRedeemers :: Map ScriptPurpose V2.Redeemer
      , txInfoData :: Map V2.DatumHash V2.Datum
      , txInfoId :: V3.TxId
      , txInfoVotes :: Map Voter (Map GovernanceActionId Vote)
      , txInfoProposalProcedures :: List ProposalProcedure
      , txInfoCurrentTreasuryAmount :: Haskell.Maybe V2.Lovelace
      , txInfoTreasuryDonation :: Haskell.Maybe V2.Lovelace
      }
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.makeLift ''TxInfo

-- | The context that the currently-executing script can access.
PlutusTx.asData
  [d|
    data ScriptContext = ScriptContext
      { scriptContextTxInfo :: TxInfo
      , -- \^ information about the transaction the currently-executing script is included in
        scriptContextRedeemer :: V2.Redeemer
      , -- \^ Redeemer for the currently-executing script
        scriptContextScriptInfo :: ScriptInfo
      }
      -- \^ the purpose of the currently-executing script, along with information associated
      -- with the purpose

      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

PlutusTx.makeLift ''ScriptContext

{-# INLINEABLE findOwnInput #-}

-- | Find the input currently being validated.
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

-- | Find the data corresponding to a data hash, if there is one
findDatum :: V2.DatumHash -> TxInfo -> Haskell.Maybe V2.Datum
findDatum dsh TxInfo {txInfoData} = lookup dsh txInfoData

{-# INLINEABLE findDatumHash #-}

{-| Find the hash of a datum, if it is part of the pending transaction's
hashes -}
findDatumHash :: V2.Datum -> TxInfo -> Haskell.Maybe V2.DatumHash
findDatumHash ds TxInfo {txInfoData} =
  PlutusTx.fst PlutusTx.<$> List.find f (toSOPList txInfoData)
  where
    f (_, ds') = ds' PlutusTx.== ds

{-# INLINEABLE findTxInByTxOutRef #-}

{-| Given a UTXO reference and a transaction (`TxInfo`), resolve it to one of the
transaction's inputs (`TxInInfo`).

Note: this only searches the true transaction inputs and not the referenced transaction inputs. -}
findTxInByTxOutRef :: V3.TxOutRef -> TxInfo -> Haskell.Maybe TxInInfo
findTxInByTxOutRef outRef TxInfo {txInfoInputs} =
  Data.List.find
    (\TxInInfo {txInInfoOutRef} -> txInInfoOutRef PlutusTx.== outRef)
    txInfoInputs

{-# INLINEABLE findContinuingOutputs #-}

{-| Find the indices of all the outputs that pay to the same script address we are
currently spending from, if any. -}
findContinuingOutputs :: ScriptContext -> List Haskell.Integer
findContinuingOutputs ctx
  | Haskell.Just TxInInfo {txInInfoResolved = V2.TxOut {txOutAddress}} <-
      findOwnInput ctx =
      Data.List.findIndices
        (f txOutAddress)
        (txInfoOutputs (scriptContextTxInfo ctx))
  where
    f addr V2.TxOut {txOutAddress = otherAddress} = addr PlutusTx.== otherAddress
findContinuingOutputs _ = PlutusTx.traceError "Le" -- "Can't find any continuing outputs"

{-# INLINEABLE getContinuingOutputs #-}

{-| Get all the outputs that pay to the same script address we are currently spending
from, if any. -}
getContinuingOutputs :: ScriptContext -> List V2.TxOut
getContinuingOutputs ctx
  | Haskell.Just TxInInfo {txInInfoResolved = V2.TxOut {txOutAddress}} <-
      findOwnInput ctx =
      Data.List.filter (f txOutAddress) (txInfoOutputs (scriptContextTxInfo ctx))
  where
    f addr V2.TxOut {txOutAddress = otherAddress} = addr PlutusTx.== otherAddress
getContinuingOutputs _ = PlutusTx.traceError "Lf" -- "Can't get any continuing outputs"

{-# INLINEABLE txSignedBy #-}

-- | Check if a transaction was signed by the given public key.
txSignedBy :: TxInfo -> V2.PubKeyHash -> Haskell.Bool
txSignedBy TxInfo {txInfoSignatories} k = case Data.List.find ((PlutusTx.==) k) txInfoSignatories of
  Haskell.Just _ -> Haskell.True
  Haskell.Nothing -> Haskell.False

{-# INLINEABLE pubKeyOutputsAt #-}

-- | Get the values paid to a public key address by a pending transaction.
pubKeyOutputsAt :: V2.PubKeyHash -> TxInfo -> List V2.Value
pubKeyOutputsAt pk p =
  let flt V2.TxOut {txOutAddress = V2.Address (V2.PubKeyCredential pk') _, txOutValue}
        | pk PlutusTx.== pk' = Haskell.Just txOutValue
      flt _ = Haskell.Nothing
   in Data.List.mapMaybe flt (txInfoOutputs p)

{-# INLINEABLE valuePaidTo #-}

-- | Get the total value paid to a public key address by a pending transaction.
valuePaidTo :: TxInfo -> V2.PubKeyHash -> V2.Value
valuePaidTo ptx pkh = Data.List.mconcat (pubKeyOutputsAt pkh ptx)

{-# INLINEABLE valueSpent #-}

-- | Get the total value of inputs spent by this transaction.
valueSpent :: TxInfo -> V2.Value
valueSpent =
  Data.List.foldMap (V2.txOutValue PlutusTx.. txInInfoResolved) PlutusTx.. txInfoInputs

{-# INLINEABLE valueProduced #-}

-- | Get the total value of outputs produced by this transaction.
valueProduced :: TxInfo -> V2.Value
valueProduced = Data.List.foldMap V2.txOutValue PlutusTx.. txInfoOutputs

{-# INLINEABLE ownCurrencySymbol #-}

-- | The 'CurrencySymbol' of the current validator script.
ownCurrencySymbol :: ScriptContext -> V2.CurrencySymbol
ownCurrencySymbol ScriptContext {scriptContextScriptInfo = MintingScript cs} = cs
ownCurrencySymbol _ =
  -- "Can't get currency symbol of the current validator script"
  PlutusTx.traceError "Lh"

{-# INLINEABLE spendsOutput #-}

{-| Check if the pending transaction spends a specific transaction output
(identified by the hash of a transaction and an index into that
transactions' outputs) -}
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
      , "Inputs:" <+> pretty txInfoInputs
      , "Reference inputs:" <+> pretty txInfoReferenceInputs
      , "Outputs:" <+> pretty txInfoOutputs
      , "Fee:" <+> pretty txInfoFee
      , "Value minted:" <+> pretty txInfoMint
      , "TxCerts:" <+> pretty txInfoTxCerts
      , "Wdrl:" <+> pretty txInfoWdrl
      , "Valid range:" <+> pretty txInfoValidRange
      , "Signatories:" <+> pretty txInfoSignatories
      , "Redeemers:" <+> pretty txInfoRedeemers
      , "Datums:" <+> pretty txInfoData
      , "Votes:" <+> pretty txInfoVotes
      , "Proposal Procedures:" <+> pretty txInfoProposalProcedures
      , "Current Treasury Amount:" <+> pretty txInfoCurrentTreasuryAmount
      , "Treasury Donation:" <+> pretty txInfoTreasuryDonation
      ]

instance Pretty ScriptContext where
  pretty ScriptContext {..} =
    vsep
      [ "ScriptInfo:" <+> pretty scriptContextScriptInfo
      , nest 2 (vsep ["TxInfo:", pretty scriptContextTxInfo])
      , nest 2 (vsep ["Redeemer:", pretty scriptContextRedeemer])
      ]
