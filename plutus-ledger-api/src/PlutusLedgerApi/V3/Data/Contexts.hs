-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fexpose-all-unfoldings #-}
-- {-# OPTIONS_GHC -ddump-simpl #-}
-- {-# OPTIONS_GHC -v #-}

module PlutusLedgerApi.V3.Data.Contexts
  ( ColdCommitteeCredential (..)
  , HotCommitteeCredential (..)
  , DRepCredential (..)
  , DRep (..)
  , Delegatee (..)
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
  , Voter (..)
  , Vote (..)
  , GovernanceActionId (..)
  , Committee (..)
  , Constitution (..)
  , ProtocolVersion (..)
  , ChangedParameters (..)
  , GovernanceAction (..)
  , ProposalProcedure (..)
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
import PlutusLedgerApi.V3.Tx qualified as V3
import PlutusTx qualified
import PlutusTx.AsData qualified as PlutusTx
import PlutusTx.Data.AssocMap
import PlutusTx.Data.List (List)
import PlutusTx.Data.List qualified as Data.List
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

data DRep
  = DRep DRepCredential
  | DRepAlwaysAbstain
  | DRepAlwaysNoConfidence
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow DRep)

PlutusTx.makeLift ''DRep
PlutusTx.makeIsDataIndexed
  ''DRep
  [ ('DRep, 0)
  , ('DRepAlwaysAbstain, 1)
  , ('DRepAlwaysNoConfidence, 2)
  ]

instance PlutusTx.Eq DRep where
  {-# INLINEABLE (==) #-}
  DRep a == DRep a'                                = a PlutusTx.== a'
  DRepAlwaysAbstain == DRepAlwaysAbstain           = Haskell.True
  DRepAlwaysNoConfidence == DRepAlwaysNoConfidence = Haskell.True
  _ == _                                           = Haskell.False

data Delegatee
  = DelegStake V2.PubKeyHash
  | DelegVote DRep
  | DelegStakeVote V2.PubKeyHash DRep
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow Delegatee)

PlutusTx.makeLift ''Delegatee
PlutusTx.makeIsDataIndexed
  ''Delegatee
  [ ('DelegStake, 0)
  , ('DelegVote, 1)
  , ('DelegStakeVote, 2)
  ]

instance PlutusTx.Eq Delegatee where
  {-# INLINEABLE (==) #-}
  DelegStake a == DelegStake a' = a PlutusTx.== a'
  DelegVote a == DelegVote a' = a PlutusTx.== a'
  DelegStakeVote a b == DelegStakeVote a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  _ == _ = Haskell.False

PlutusTx.asData
  [d|
    data TxCert
      = -- | Register staking credential with an optional deposit amount
        TxCertRegStaking V2.Credential (Haskell.Maybe V2.Lovelace)
      | -- | Un-Register staking credential with an optional refund amount
        TxCertUnRegStaking V2.Credential (Haskell.Maybe V2.Lovelace)
      | -- | Delegate staking credential to a Delegatee
        TxCertDelegStaking V2.Credential Delegatee
      | -- | Register and delegate staking credential to a Delegatee in one certificate. Noter that
        -- deposit is mandatory.
        TxCertRegDeleg V2.Credential Delegatee V2.Lovelace
      | -- | Register a DRep with a deposit value. The optional anchor is omitted.
        TxCertRegDRep DRepCredential V2.Lovelace
      | -- | Update a DRep. The optional anchor is omitted.
        TxCertUpdateDRep DRepCredential
      | -- | UnRegister a DRep with mandatory refund value
        TxCertUnRegDRep DRepCredential V2.Lovelace
      | -- | A digest of the PoolParams
        TxCertPoolRegister
          V2.PubKeyHash
          -- ^ poolId
          V2.PubKeyHash
          -- ^ pool VFR
      | -- | The retirement certificate and the Epoch in which the retirement will take place
        TxCertPoolRetire V2.PubKeyHash Haskell.Integer
      | -- | Authorize a Hot credential for a specific Committee member's cold credential
        TxCertAuthHotCommittee ColdCommitteeCredential HotCommitteeCredential
      | TxCertResignColdCommittee ColdCommitteeCredential
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
      deriving (Pretty) via (PrettyShow TxCert)
  |]

PlutusTx.makeLift ''TxCert

instance PlutusTx.Eq TxCert where
  {-# INLINEABLE (==) #-}
  TxCertRegStaking a b == TxCertRegStaking a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  TxCertUnRegStaking a b == TxCertUnRegStaking a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  TxCertDelegStaking a b == TxCertDelegStaking a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  TxCertRegDeleg a b c == TxCertRegDeleg a' b' c' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b' PlutusTx.&& c PlutusTx.== c'
  TxCertRegDRep a b == TxCertRegDRep a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  TxCertUpdateDRep a == TxCertUpdateDRep a' =
    a PlutusTx.== a'
  TxCertUnRegDRep a b == TxCertUnRegDRep a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  TxCertAuthHotCommittee a b == TxCertAuthHotCommittee a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  TxCertResignColdCommittee a == TxCertResignColdCommittee a' =
    a PlutusTx.== a'
  _ == _ = Haskell.False

data Voter
  = CommitteeVoter HotCommitteeCredential
  | DRepVoter DRepCredential
  | StakePoolVoter V2.PubKeyHash
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow Voter)

PlutusTx.makeLift ''Voter
PlutusTx.makeIsDataIndexed
  ''Voter
  [ ('CommitteeVoter, 0)
  , ('DRepVoter, 1)
  , ('StakePoolVoter, 2)
  ]

instance PlutusTx.Eq Voter where
  {-# INLINEABLE (==) #-}
  CommitteeVoter a == CommitteeVoter a' =
    a PlutusTx.== a'
  DRepVoter a == DRepVoter a' =
    a PlutusTx.== a'
  StakePoolVoter a == StakePoolVoter a' =
    a PlutusTx.== a'
  _ == _ = Haskell.False

-- | A vote. The optional anchor is omitted.
data Vote
  = VoteNo
  | VoteYes
  | Abstain
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow Vote)

PlutusTx.makeLift ''Vote
PlutusTx.makeIsDataIndexed
  ''Vote
  [ ('VoteNo, 0)
  , ('VoteYes, 1)
  , ('Abstain, 2)
  ]

instance PlutusTx.Eq Vote where
  {-# INLINEABLE (==) #-}
  VoteNo == VoteNo   = Haskell.True
  VoteYes == VoteYes = Haskell.True
  Abstain == Abstain = Haskell.True
  _ == _             = Haskell.False

-- | Similar to TxOutRef, but for GovActions
data GovernanceActionId = GovernanceActionId
  { gaidTxId        :: V3.TxId
  , gaidGovActionIx :: Haskell.Integer
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)

PlutusTx.makeLift ''GovernanceActionId
PlutusTx.makeIsDataIndexed ''GovernanceActionId [('GovernanceActionId, 0)]

instance Pretty GovernanceActionId where
  pretty GovernanceActionId{..} =
    vsep
      [ "gaidTxId:" <+> pretty gaidTxId
      , "gaidGovActionIx:" <+> pretty gaidGovActionIx
      ]

instance PlutusTx.Eq GovernanceActionId where
  {-# INLINEABLE (==) #-}
  GovernanceActionId a b == GovernanceActionId a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'

data Committee = Committee
  { committeeMembers :: Map ColdCommitteeCredential Haskell.Integer
  -- ^ Committee members with epoch number when each of them expires
  , committeeQuorum  :: PlutusTx.Rational
  -- ^ Quorum of the committee that is necessary for a successful vote
  }
  deriving stock (Generic, Haskell.Show)

PlutusTx.makeLift ''Committee
PlutusTx.makeIsDataIndexed ''Committee [('Committee, 0)]

instance Pretty Committee where
  pretty Committee{..} =
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

PlutusTx.makeLift ''Constitution
PlutusTx.makeIsDataIndexed ''Constitution [('Constitution, 0)]

instance Pretty Constitution where
  pretty (Constitution script) = "constitutionScript:" <+> pretty script

instance PlutusTx.Eq Constitution where
  {-# INLINEABLE (==) #-}
  Constitution a == Constitution a' = a PlutusTx.== a'

data ProtocolVersion = ProtocolVersion
  { pvMajor :: Haskell.Integer
  , pvMinor :: Haskell.Integer
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)

PlutusTx.makeLift ''ProtocolVersion
PlutusTx.makeIsDataIndexed ''ProtocolVersion [('ProtocolVersion, 0)]

instance Pretty ProtocolVersion where
  pretty ProtocolVersion{..} =
    vsep
      [ "pvMajor:" <+> pretty pvMajor
      , "pvMinor:" <+> pretty pvMinor
      ]

instance PlutusTx.Eq ProtocolVersion where
  {-# INLINEABLE (==) #-}
  ProtocolVersion a b == ProtocolVersion a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'

{- | A Plutus Data object containing proposed parameter changes. The Data object contains
a @Map@ with one entry per changed parameter, from the parameter ID to the new value.
Unchanged parameters are not included.

The mapping from parameter IDs to parameters can be found in
[conway.cddl](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl).

/Invariant:/ This map is non-empty, and the keys are stored in ascending order.
-}
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

data GovernanceAction
  = ParameterChange
      (Haskell.Maybe GovernanceActionId)
      ChangedParameters
      (Haskell.Maybe V2.ScriptHash) -- ^ Hash of the constitution script
  | -- | proposal to update protocol version
    HardForkInitiation (Haskell.Maybe GovernanceActionId) ProtocolVersion
  | TreasuryWithdrawals
      (Map V2.Credential V2.Lovelace)
      (Haskell.Maybe V2.ScriptHash) -- ^ Hash of the constitution script
  | NoConfidence (Haskell.Maybe GovernanceActionId)
  | UpdateCommittee
      (Haskell.Maybe GovernanceActionId)
      (List ColdCommitteeCredential) -- ^ Committee members to be removed
      (Map ColdCommitteeCredential Haskell.Integer) -- ^ Committee members to be added
      Rational -- ^ New quorum
  | NewConstitution (Haskell.Maybe GovernanceActionId) Constitution
  | InfoAction
  deriving stock (Generic, Haskell.Show)
  deriving (Pretty) via (PrettyShow GovernanceAction)

PlutusTx.makeLift ''GovernanceAction
PlutusTx.makeIsDataIndexed
  ''GovernanceAction
  [ ('ParameterChange, 0)
  , ('HardForkInitiation, 1)
  , ('TreasuryWithdrawals, 2)
  , ('NoConfidence, 3)
  , ('UpdateCommittee, 4)
  , ('NewConstitution, 5)
  , ('InfoAction, 6)
  ]

-- | A proposal procedure. The optional anchor is omitted.
data ProposalProcedure = ProposalProcedure
  { ppDeposit          :: V2.Lovelace
  , ppReturnAddr       :: V2.Credential
  , ppGovernanceAction :: GovernanceAction
  }
  deriving stock (Generic, Haskell.Show)

PlutusTx.makeLift ''ProposalProcedure
PlutusTx.makeIsDataIndexed ''ProposalProcedure [('ProposalProcedure, 0)]

instance Pretty ProposalProcedure where
  pretty ProposalProcedure{..} =
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
          -- ^ 0-based index of the given `TxCert` in `txInfoTxCerts`
          TxCert
      | Voting Voter
      | Proposing
          Haskell.Integer
          -- ^ 0-based index of the given `ProposalProcedure` in `txInfoProposalProcedures`
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
          -- ^ 0-based index of the given `TxCert` in `txInfoTxCerts`
          TxCert
      | VotingScript Voter
      | ProposingScript
          Haskell.Integer
          -- ^ 0-based index of the given `ProposalProcedure` in `txInfoProposalProcedures`
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
      { txInInfoOutRef   :: V3.TxOutRef
      , txInInfoResolved :: V2.TxOut
      }
      deriving stock (Generic, Haskell.Show, Haskell.Eq)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
  |]

PlutusTx.makeLift ''TxInInfo

instance PlutusTx.Eq TxInInfo where
  TxInInfo ref res == TxInInfo ref' res' =
    ref PlutusTx.== ref' PlutusTx.&& res PlutusTx.== res'

instance Pretty TxInInfo where
  pretty TxInInfo{txInInfoOutRef, txInInfoResolved} =
    pretty txInInfoOutRef <+> "->" <+> pretty txInInfoResolved

-- | TxInfo for PlutusV3
PlutusTx.asData
  [d|
    data TxInfo = TxInfo
      { txInfoInputs                :: List TxInInfo
      , txInfoReferenceInputs       :: List TxInInfo
      , txInfoOutputs               :: List V2.TxOut
      , txInfoFee                   :: V2.Lovelace
      , txInfoMint                  :: V2.Value
      -- ^ The 'Value' minted by this transaction.
      --
      -- /Invariant:/ This field does not contain Ada with zero quantity, unlike
      -- their namesakes in Plutus V1 and V2's ScriptContexts.
      , txInfoTxCerts               :: List TxCert
      , txInfoWdrl                  :: Map V2.Credential V2.Lovelace
      , txInfoValidRange            :: V2.POSIXTimeRange
      , txInfoSignatories           :: List V2.PubKeyHash
      , txInfoRedeemers             :: Map ScriptPurpose V2.Redeemer
      , txInfoData                  :: Map V2.DatumHash V2.Datum
      , txInfoId                    :: V3.TxId
      , txInfoVotes                 :: Map Voter (Map GovernanceActionId Vote)
      , txInfoProposalProcedures    :: List ProposalProcedure
      , txInfoCurrentTreasuryAmount :: Haskell.Maybe V2.Lovelace
      , txInfoTreasuryDonation      :: Haskell.Maybe V2.Lovelace
      }
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
    |]

{-# INLINEABLE TxInfo #-}
{-# INLINEABLE txInfoInputs #-}
{-# INLINEABLE txInfoReferenceInputs #-}
{-# INLINEABLE txInfoOutputs #-}
{-# INLINEABLE txInfoFee #-}
{-# INLINEABLE txInfoMint #-}
{-# INLINEABLE txInfoTxCerts #-}
{-# INLINEABLE txInfoWdrl #-}
{-# INLINEABLE txInfoValidRange #-}
{-# INLINEABLE txInfoSignatories #-}
{-# INLINEABLE txInfoRedeemers #-}
{-# INLINEABLE txInfoData #-}
{-# INLINEABLE txInfoId #-}
{-# INLINEABLE txInfoVotes #-}
{-# INLINEABLE txInfoProposalProcedures #-}
{-# INLINEABLE txInfoCurrentTreasuryAmount #-}
{-# INLINEABLE txInfoTreasuryDonation #-}

PlutusTx.makeLift ''TxInfo

-- | The context that the currently-executing script can access.
PlutusTx.asData
  [d|
    data ScriptContext = ScriptContext
      { scriptContextTxInfo     :: TxInfo
      -- ^ information about the transaction the currently-executing script is included in
      , scriptContextRedeemer   :: V2.Redeemer
      -- ^ Redeemer for the currently-executing script
      , scriptContextScriptInfo :: ScriptInfo
      -- ^ the purpose of the currently-executing script, along with information associated
      -- with the purpose
      }
      deriving stock (Generic, Haskell.Show)
      deriving newtype (PlutusTx.FromData, PlutusTx.UnsafeFromData, PlutusTx.ToData)
  |]

{-# INLINEABLE ScriptContext #-}
{-# INLINEABLE scriptContextTxInfo #-}
{-# INLINEABLE scriptContextRedeemer #-}
{-# INLINEABLE scriptContextScriptInfo #-}

PlutusTx.makeLift ''ScriptContext

{-# INLINEABLE findOwnInput #-}

-- | Find the input currently being validated.
findOwnInput :: ScriptContext -> Haskell.Maybe TxInInfo
findOwnInput
  ScriptContext
    { scriptContextTxInfo = TxInfo{txInfoInputs}
    , scriptContextScriptInfo = SpendingScript txOutRef _
    } =
    Data.List.find
      (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef PlutusTx.== txOutRef)
      txInfoInputs
findOwnInput _ = Haskell.Nothing

{-# INLINEABLE findDatum #-}

-- | Find the data corresponding to a data hash, if there is one
findDatum :: V2.DatumHash -> TxInfo -> Haskell.Maybe V2.Datum
findDatum dsh TxInfo{txInfoData} = lookup dsh txInfoData

{-# INLINEABLE findDatumHash #-}

{- | Find the hash of a datum, if it is part of the pending transaction's
hashes
-}
findDatumHash :: V2.Datum -> TxInfo -> Haskell.Maybe V2.DatumHash
findDatumHash ds TxInfo{txInfoData} =
  PlutusTx.fst PlutusTx.<$> PlutusTx.find f (toList txInfoData)
  where
    f (_, ds') = ds' PlutusTx.== ds

{-# INLINEABLE findTxInByTxOutRef #-}

{- | Given a UTXO reference and a transaction (`TxInfo`), resolve it to one of the
transaction's inputs (`TxInInfo`).

Note: this only searches the true transaction inputs and not the referenced transaction inputs.
-}
findTxInByTxOutRef :: V3.TxOutRef -> TxInfo -> Haskell.Maybe TxInInfo
findTxInByTxOutRef outRef TxInfo{txInfoInputs} =
  Data.List.find
    (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef PlutusTx.== outRef)
    txInfoInputs

{-# INLINEABLE findContinuingOutputs #-}

{- | Find the indices of all the outputs that pay to the same script address we are
currently spending from, if any.
-}
findContinuingOutputs :: ScriptContext -> List Haskell.Integer
findContinuingOutputs ctx
  | Haskell.Just TxInInfo{txInInfoResolved = V2.TxOut{txOutAddress}} <-
      findOwnInput ctx =
      Data.List.findIndices
        (f txOutAddress)
        (txInfoOutputs (scriptContextTxInfo ctx))
  where
    f addr V2.TxOut{txOutAddress = otherAddress} = addr PlutusTx.== otherAddress
findContinuingOutputs _ = PlutusTx.traceError "Le" -- "Can't find any continuing outputs"

{-# INLINEABLE getContinuingOutputs #-}

{- | Get all the outputs that pay to the same script address we are currently spending
from, if any.
-}
getContinuingOutputs :: ScriptContext -> List V2.TxOut
getContinuingOutputs ctx
  | Haskell.Just TxInInfo{txInInfoResolved = V2.TxOut{txOutAddress}} <-
      findOwnInput ctx =
      Data.List.filter (f txOutAddress) (txInfoOutputs (scriptContextTxInfo ctx))
  where
    f addr V2.TxOut{txOutAddress = otherAddress} = addr PlutusTx.== otherAddress
getContinuingOutputs _ = PlutusTx.traceError "Lf" -- "Can't get any continuing outputs"

{-# INLINEABLE txSignedBy #-}

-- | Check if a transaction was signed by the given public key.
txSignedBy :: TxInfo -> V2.PubKeyHash -> Haskell.Bool
txSignedBy TxInfo{txInfoSignatories} k = case Data.List.find ((PlutusTx.==) k) txInfoSignatories of
  Haskell.Just _  -> Haskell.True
  Haskell.Nothing -> Haskell.False

{-# INLINEABLE pubKeyOutputsAt #-}

-- | Get the values paid to a public key address by a pending transaction.
pubKeyOutputsAt :: V2.PubKeyHash -> TxInfo -> List V2.Value
pubKeyOutputsAt pk p =
  let flt V2.TxOut{txOutAddress = V2.Address (V2.PubKeyCredential pk') _, txOutValue}
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
ownCurrencySymbol ScriptContext{scriptContextScriptInfo = MintingScript cs} = cs
ownCurrencySymbol _ =
  -- "Can't get currency symbol of the current validator script"
  PlutusTx.traceError "Lh"

{-# INLINEABLE spendsOutput #-}

{- | Check if the pending transaction spends a specific transaction output
(identified by the hash of a transaction and an index into that
transactions' outputs)
-}
spendsOutput :: TxInfo -> V3.TxId -> Haskell.Integer -> Haskell.Bool
spendsOutput txInfo txId i =
  let spendsOutRef inp =
        let outRef = txInInfoOutRef inp
         in txId PlutusTx.== V3.txOutRefId outRef
              PlutusTx.&& i PlutusTx.== V3.txOutRefIdx outRef
   in Data.List.any spendsOutRef (txInfoInputs txInfo)

instance Pretty TxInfo where
  pretty TxInfo{..} =
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
  pretty ScriptContext{..} =
    vsep
      [ "ScriptInfo:" <+> pretty scriptContextScriptInfo
      , nest 2 (vsep ["TxInfo:", pretty scriptContextTxInfo])
      , nest 2 (vsep ["Redeemer:", pretty scriptContextRedeemer])
      ]
