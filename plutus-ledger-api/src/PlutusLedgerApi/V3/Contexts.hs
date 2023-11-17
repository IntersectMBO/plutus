{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}

module PlutusLedgerApi.V3.Contexts where

import GHC.Generics (Generic)
import Prettyprinter (nest, vsep, (<+>))
import Prettyprinter.Extras

import PlutusLedgerApi.V2 qualified as V2
import PlutusTx qualified
import PlutusTx.AssocMap hiding (filter, mapMaybe)
import PlutusTx.Prelude qualified as PlutusTx

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

data DRep
  = DRep DRepCredential
  | DRepAlwaysAbstain
  | DRepAlwaysNoConfidence
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow DRep)

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

instance PlutusTx.Eq Delegatee where
  {-# INLINEABLE (==) #-}
  DelegStake a == DelegStake a' = a PlutusTx.== a'
  DelegVote a == DelegVote a' = a PlutusTx.== a'
  DelegStakeVote a b == DelegStakeVote a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  _ == _ = Haskell.False

data TxCert
  = -- | Register staking credential with an optional deposit amount
    TxCertRegStaking V2.Credential (Haskell.Maybe V2.Value)
  | -- | Un-Register staking credential with an optional refund amount
    TxCertUnRegStaking V2.Credential (Haskell.Maybe V2.Value)
  | -- | Delegate staking credential to a Delegatee
    TxCertDelegStaking V2.Credential Delegatee
  | -- | Register and delegate staking credential to a Delegatee in one certificate. Noter that
    -- deposit is mandatory.
    TxCertRegDeleg V2.Credential Delegatee V2.Value
  | -- | Register a DRep with a deposit value. The optional anchor is omitted.
    TxCertRegDRep DRepCredential V2.Value
  | -- | Update a DRep. The optional anchor is omitted.
    TxCertUpdateDRep DRepCredential
  | -- | UnRegister a DRep with mandatory refund value
    TxCertUnRegDRep DRepCredential V2.Value
  | -- | Authorize a Hot credential for a specific Committee member's cold credential
    TxCertAuthHotCommittee ColdCommitteeCredential HotCommitteeCredential
  | TxCertResignColdCommittee ColdCommitteeCredential
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow TxCert)

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

instance PlutusTx.Eq Vote where
  {-# INLINEABLE (==) #-}
  VoteNo == VoteNo   = Haskell.True
  VoteYes == VoteYes = Haskell.True
  Abstain == Abstain = Haskell.True
  _ == _             = Haskell.False

-- | Similar to TxOutRef, but for GovActions
data GovernanceActionId = GovernanceActionId
  { gaidTxId        :: V2.TxId
  , gaidGovActionIx :: Haskell.Integer
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)

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
  deriving stock (Generic, Haskell.Show, Haskell.Eq)

instance Pretty Committee where
  pretty Committee{..} =
    vsep
      [ "committeeMembers:" <+> pretty committeeMembers
      , "committeeQuorum:" <+> pretty committeeQuorum
      ]

instance PlutusTx.Eq Committee where
  {-# INLINEABLE (==) #-}
  Committee a b == Committee a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'

-- | A constitution. The optional anchor is omitted.
newtype Constitution = Constitution
  { constitutionScript :: Haskell.Maybe V2.ScriptHash
  }
  deriving stock (Generic)
  deriving newtype (Haskell.Show, Haskell.Eq)

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

-- | A Plutus Data object containing proposed parameter changes. The Data object contains
-- a @Map@ with one entry per changed parameter, from the parameter name to the new value.
-- Unchanged parameters are not included.
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

data GovernanceAction
  = ParameterChange (Haskell.Maybe GovernanceActionId) ChangedParameters
  | -- | proposal to update protocol version
    HardForkInitiation (Haskell.Maybe GovernanceActionId) ProtocolVersion
  | TreasuryWithdrawals (Map V2.Credential V2.Value)
  | NoConfidence (Haskell.Maybe GovernanceActionId)
  | NewCommittee
      (Haskell.Maybe GovernanceActionId)
      [ColdCommitteeCredential] -- ^ Old committee
      Committee -- ^ New Committee
  | NewConstitution (Haskell.Maybe GovernanceActionId) Constitution
  | InfoAction
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow GovernanceAction)

instance PlutusTx.Eq GovernanceAction where
  {-# INLINEABLE (==) #-}
  ParameterChange a b == ParameterChange a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  HardForkInitiation a b == HardForkInitiation a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  TreasuryWithdrawals a == TreasuryWithdrawals a' = a PlutusTx.== a'
  NoConfidence a == NoConfidence a' = a PlutusTx.== a'
  NewCommittee a b c == NewCommittee a' b' c' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b' PlutusTx.&& c PlutusTx.== c'
  NewConstitution a b == NewConstitution a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  InfoAction == InfoAction = Haskell.True
  _ == _ = Haskell.False

-- | A proposal procedure. The optional anchor is omitted.
data ProposalProcedure = ProposalProcedure
  { ppDeposit          :: V2.Value
  , ppReturnAddr       :: V2.Credential
  , ppGovernanceAction :: GovernanceAction
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)

instance Pretty ProposalProcedure where
  pretty ProposalProcedure{..} =
    vsep
      [ "ppDeposit:" <+> pretty ppDeposit
      , "ppReturnAddr:" <+> pretty ppReturnAddr
      , "ppGovernanceAction:" <+> pretty ppGovernanceAction
      ]

instance PlutusTx.Eq ProposalProcedure where
  {-# INLINEABLE (==) #-}
  ProposalProcedure a b c == ProposalProcedure a' b' c' =
    a PlutusTx.== a'
      PlutusTx.&& b PlutusTx.== b'
      PlutusTx.&& c PlutusTx.== c'

data ScriptPurpose
  = Minting V2.CurrencySymbol
  | Spending V2.TxOutRef
  | Rewarding V2.Credential
  | Certifying TxCert
  | Voting Voter GovernanceActionId
  | Proposing Haskell.Integer
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow ScriptPurpose)

instance PlutusTx.Eq ScriptPurpose where
  {-# INLINEABLE (==) #-}
  Minting a == Minting a' =
    a PlutusTx.== a'
  Spending a == Spending a' =
    a PlutusTx.== a'
  Rewarding a == Rewarding a' =
    a PlutusTx.== a'
  Certifying a == Certifying a' =
    a PlutusTx.== a'
  Voting a b == Voting a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  Proposing a == Proposing a' =
    a PlutusTx.== a'
  _ == _ = Haskell.False

-- | TxInfo for PlutusV3
data TxInfo = TxInfo
  { txInfoInputs                :: [V2.TxInInfo]
  , txInfoReferenceInputs       :: [V2.TxInInfo]
  , txInfoOutputs               :: [V2.TxOut]
  , txInfoFee                   :: V2.Value
  , txInfoMint                  :: V2.Value
  , txInfoTxCerts               :: [TxCert]
  , txInfoWdrl                  :: Map V2.Credential Haskell.Integer
  , txInfoValidRange            :: V2.POSIXTimeRange
  , txInfoSignatories           :: [V2.PubKeyHash]
  , txInfoRedeemers             :: Map ScriptPurpose V2.Redeemer
  , txInfoData                  :: Map V2.DatumHash V2.Datum
  , txInfoId                    :: V2.TxId
  , txInfoVotes                 :: Map Voter (Map GovernanceActionId Vote)
  , txInfoProposalProcedures    :: [ProposalProcedure]
  , txInfoCurrentTreasuryAmount :: Haskell.Maybe V2.Value
  , txInfoTreasuryDonation      :: Haskell.Maybe V2.Value
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)

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

instance PlutusTx.Eq TxInfo where
  {-# INLINEABLE (==) #-}
  TxInfo a b c d e f g h i j k l m n o p
    == TxInfo a' b' c' d' e' f' g' h' i' j' k' l' m' n' o' p' =
      a PlutusTx.== a'
        PlutusTx.&& b PlutusTx.== b'
        PlutusTx.&& c PlutusTx.== c'
        PlutusTx.&& d PlutusTx.== d'
        PlutusTx.&& e PlutusTx.== e'
        PlutusTx.&& f PlutusTx.== f'
        PlutusTx.&& g PlutusTx.== g'
        PlutusTx.&& h PlutusTx.== h'
        PlutusTx.&& i PlutusTx.== i'
        PlutusTx.&& j PlutusTx.== j'
        PlutusTx.&& k PlutusTx.== k'
        PlutusTx.&& l PlutusTx.== l'
        PlutusTx.&& m PlutusTx.== m'
        PlutusTx.&& n PlutusTx.== n'
        PlutusTx.&& o PlutusTx.== o'
        PlutusTx.&& p PlutusTx.== p'

-- | The context that the currently-executing script can access.
data ScriptContext = ScriptContext
  { scriptContextTxInfo  :: TxInfo
  -- ^ information about the transaction the currently-executing script is included in
  , scriptContextPurpose :: ScriptPurpose
  -- ^ the purpose of the currently-executing script
  }
  deriving stock (Generic, Haskell.Eq, Haskell.Show)

instance Pretty ScriptContext where
  pretty ScriptContext{..} =
    vsep
      [ "Purpose:" <+> pretty scriptContextPurpose
      , nest 2 (vsep ["TxInfo:", pretty scriptContextTxInfo])
      ]

instance PlutusTx.Eq ScriptContext where
  {-# INLINEABLE (==) #-}
  ScriptContext a b == ScriptContext a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'

PlutusTx.makeLift ''ColdCommitteeCredential
PlutusTx.makeLift ''HotCommitteeCredential
PlutusTx.makeLift ''DRepCredential

PlutusTx.makeLift ''DRep
PlutusTx.makeIsDataIndexed
  ''DRep
  [ ('DRep, 0)
  , ('DRepAlwaysAbstain, 1)
  , ('DRepAlwaysNoConfidence, 2)
  ]

PlutusTx.makeLift ''Delegatee
PlutusTx.makeIsDataIndexed
  ''Delegatee
  [ ('DelegStake, 0)
  , ('DelegVote, 1)
  , ('DelegStakeVote, 2)
  ]

PlutusTx.makeLift ''TxCert
PlutusTx.makeIsDataIndexed
  ''TxCert
  [ ('TxCertRegStaking, 0)
  , ('TxCertUnRegStaking, 1)
  , ('TxCertDelegStaking, 2)
  , ('TxCertRegDeleg, 3)
  , ('TxCertRegDRep, 4)
  , ('TxCertUpdateDRep, 5)
  , ('TxCertUnRegDRep, 6)
  , ('TxCertAuthHotCommittee, 7)
  , ('TxCertResignColdCommittee, 8)
  ]

PlutusTx.makeLift ''Voter
PlutusTx.makeIsDataIndexed
  ''Voter
  [ ('CommitteeVoter, 0)
  , ('DRepVoter, 1)
  , ('StakePoolVoter, 2)
  ]

PlutusTx.makeLift ''Vote
PlutusTx.makeIsDataIndexed
  ''Vote
  [ ('VoteNo, 0)
  , ('VoteYes, 1)
  , ('Abstain, 2)
  ]

PlutusTx.makeLift ''GovernanceActionId
PlutusTx.makeIsDataIndexed ''GovernanceActionId [('GovernanceActionId, 0)]

PlutusTx.makeLift ''Committee
PlutusTx.makeIsDataIndexed ''Committee [('Committee, 0)]

PlutusTx.makeLift ''Constitution
PlutusTx.makeIsDataIndexed ''Constitution [('Constitution, 0)]

PlutusTx.makeLift ''ProtocolVersion
PlutusTx.makeIsDataIndexed ''ProtocolVersion [('ProtocolVersion, 0)]

PlutusTx.makeLift ''ChangedParameters
PlutusTx.makeLift ''GovernanceAction
PlutusTx.makeIsDataIndexed
  ''GovernanceAction
  [ ('ParameterChange, 0)
  , ('HardForkInitiation, 1)
  , ('TreasuryWithdrawals, 2)
  , ('NoConfidence, 3)
  , ('NewCommittee, 4)
  , ('NewConstitution, 5)
  , ('InfoAction, 6)
  ]

PlutusTx.makeLift ''ProposalProcedure
PlutusTx.makeIsDataIndexed ''ProposalProcedure [('ProposalProcedure, 0)]

PlutusTx.makeLift ''ScriptPurpose
PlutusTx.makeIsDataIndexed
  ''ScriptPurpose
  [ ('Minting, 0)
  , ('Spending, 1)
  , ('Rewarding, 2)
  , ('Certifying, 3)
  , ('Voting, 4)
  , ('Proposing, 5)
  ]

PlutusTx.makeLift ''TxInfo
PlutusTx.makeIsDataIndexed ''TxInfo [('TxInfo, 0)]

PlutusTx.makeLift ''ScriptContext
PlutusTx.makeIsDataIndexed ''ScriptContext [('ScriptContext, 0)]
