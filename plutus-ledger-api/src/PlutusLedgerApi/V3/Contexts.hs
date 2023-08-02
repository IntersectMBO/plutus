{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
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
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow ColdCommitteeHash)
  deriving newtype
    ( PlutusTx.Eq
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )

newtype HotCommitteeCredential = HotCommitteeCredential V2.Credential
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow HotCommitteeHash)
  deriving newtype
    ( PlutusTx.Eq
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )

newtype DRepHash = DRepHash V2.Credential
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow DRepHash)
  deriving newtype
    ( PlutusTx.Eq
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )

data DRep
  = DRepCredential DRepHash
  | DRepAlwaysAbstain
  | DRepAlwaysNoConfidence
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow DRep)

instance PlutusTx.Eq DRep where
  {-# INLINEABLE (==) #-}
  DRepCredential a == DRepCredential a'            = a PlutusTx.== a'
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

{- | There is probably no need for Plutus Scripts to even know about all this data in Anchors,
but it is here for completeness. So we might wanna omit them, especially since urls are a
bit tricky, since we can't guarantee their validity, not even that they are utf8-encoded.
-}
data Anchor = Anchor
  { anchorUrl      :: PlutusTx.BuiltinByteString -- Arbitrary Url
  , anchorDataHash :: PlutusTx.BuiltinByteString -- Blake2b_256 of some off-chain data
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)

instance Pretty Anchor where
  pretty Anchor{..} =
    vsep
      [ "anchorUrl:" <+> pretty anchorUrl
      , "anchorDataHash:" <+> pretty anchorDataHash
      ]

instance PlutusTx.Eq Anchor where
  {-# INLINEABLE (==) #-}
  Anchor a b == Anchor a' b' = a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'

{- | Note that it no longer is called DCert, since certificates are no longer all about
delegation, they are also about governance.

Notable changes:

* Pool certificates are unchanged
* Addition of deposits and refunds. Those values are validated according to respectful
  PParams. Certificates that where present before get their deposit/refund as
  optional. This is done for graceful tarnsition, since next era after Conway will require
  deposit/refund amount
* New DRep entity
* New Constitutional Committee entity
-}
data TxCert
  = -- | Register staking credential with an optional deposit amount
    TxCertRegStaking V2.StakingCredential (Haskell.Maybe V2.Value)
  | -- | Un-Register staking credential with an optional refund amount
    TxCertUnRegStaking V2.StakingCredential (Haskell.Maybe V2.Value)
  | -- | Delegate staking credential to a Delegatee
    TxCertDelegStaking V2.StakingCredential Delegatee
  | -- | Register and delegate staking credential to a Delegatee in one certificate. Noter that
    -- deposit is mandatory.
    TxCertRegDeleg V2.StakingCredential Delegatee V2.Value
  | -- | Register a DRep with mandatory deposit value and an optional Anchor
    TxCertRegDRep DRepHash V2.Value (Haskell.Maybe Anchor)
  | -- | Update DRep's optional Anchor
    TxCertUpdateDRep DRepHash (Haskell.Maybe Anchor)
  | -- | UnRegister a DRep with mandatory refund value
    TxCertUnRegDRep DRepHash V2.Value
  | -- | Authorize a Hot credential for a specific Committee member's cold credential
    TxCertAuthHotCommittee ColdCommitteeHash HotCommitteeHash
  | TxCertResignColdCommittee ColdCommitteeHash
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
  TxCertRegDRep a b c == TxCertRegDRep a' b' c' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b' PlutusTx.&& c PlutusTx.== c'
  TxCertUpdateDRep a b == TxCertUpdateDRep a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  TxCertUnRegDRep a b == TxCertUnRegDRep a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  TxCertAuthHotCommittee a b == TxCertAuthHotCommittee a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  TxCertResignColdCommittee a == TxCertResignColdCommittee a' =
    a PlutusTx.== a'
  _ == _ = Haskell.False

data Voter
  = CommitteeVoter !HotCommitteeHash
  | DRepVoter DRepHash
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

data VotingProcedure = VotingProcedure
  { vpVote   :: Vote
  , vpAnchor :: Haskell.Maybe Anchor
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)

instance Pretty VotingProcedure where
  pretty VotingProcedure{..} =
    vsep
      [ "vpVote:" <+> pretty vpVote
      , "vpAnchor:" <+> pretty vpAnchor
      ]

instance PlutusTx.Eq VotingProcedure where
  {-# INLINEABLE (==) #-}
  VotingProcedure a b == VotingProcedure a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'

data Committee = Committee
  { committeeMembers :: Map ColdCommitteeHash Haskell.Integer
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

data Constitution = Constitution
  { constitutionHash   :: PlutusTx.BuiltinByteString -- Balke2b_256 of some off-chain data
  , constitutionScript :: Haskell.Maybe V2.ScriptHash
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)

instance Pretty Constitution where
  pretty Constitution{..} =
    vsep
      [ "constitutionHash:" <+> pretty constitutionHash
      , "constitutionScript:" <+> pretty constitutionScript
      ]

instance PlutusTx.Eq Constitution where
  {-# INLINEABLE (==) #-}
  Constitution a b == Constitution a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'

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

data GovernanceAction
  = -- | Proposed updates to PParams. This is a very tricky one, since PParamsUpdate is pretty
    -- big and changes from one era to another. However, it could be very important for the
    -- governance scripts to be able to see the values in the PParamsUpdate, but I am not
    -- sure how to go forward about this, so for now I leave it as empty.
    ParameterChange -- Should contain: (PParamsUpdate era)
    --
  | -- | proposal to update protocol version
    HardForkInitiation ProtocolVersion
  | TreasuryWithdrawals !(Map V2.Credential V2.Value)
  | NoConfidence
  | NewCommittee
      -- | Old committee
      [ColdCommitteeHash]
      -- | New Committee
      Committee
  | NewConstitution Constitution
  | InfoAction
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow GovernanceAction)

instance PlutusTx.Eq GovernanceAction where
  {-# INLINEABLE (==) #-}
  ParameterChange == ParameterChange = Haskell.True
  HardForkInitiation a == HardForkInitiation a' = a PlutusTx.== a'
  TreasuryWithdrawals a == TreasuryWithdrawals a' = a PlutusTx.== a'
  NoConfidence == NoConfidence = Haskell.True
  NewCommittee a b == NewCommittee a' b' =
    a PlutusTx.== a' PlutusTx.&& b PlutusTx.== b'
  NewConstitution a == NewConstitution a' = a PlutusTx.== a'
  InfoAction == InfoAction = Haskell.True
  _ == _ = Haskell.False

data ProposalProcedure = ProposalProcedure
  { ppDeposit          :: V2.Value
  , ppReturnAddr       :: V2.Credential
  , ppGovernanceAction :: GovernanceAction
  , ppAnchor           :: Anchor
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)

instance Pretty ProposalProcedure where
  pretty ProposalProcedure{..} =
    vsep
      [ "ppDeposit:" <+> pretty ppDeposit
      , "ppReturnAddr:" <+> pretty ppReturnAddr
      , "ppGovernanceAction:" <+> pretty ppGovernanceAction
      , "ppAnchor:" <+> pretty ppAnchor
      ]

instance PlutusTx.Eq ProposalProcedure where
  {-# INLINEABLE (==) #-}
  ProposalProcedure a b c d == ProposalProcedure a' b' c' d' =
    a PlutusTx.== a'
      PlutusTx.&& b PlutusTx.== b'
      PlutusTx.&& c PlutusTx.== c'
      PlutusTx.&& d PlutusTx.== d'

data ScriptPurpose
  = Minting V2.CurrencySymbol
  | Spending V2.TxOutRef
  | Rewarding V2.StakingCredential
  | Certifying TxCert
  | Voting Voter GovernanceActionId
  | Proposing -- For now this will only be used by Constitution, thus might turned out to be
  -- unused.
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
  Proposing == Proposing = Haskell.True
  _ == _ = Haskell.False

-- | TxInfo for PlutusV3
data TxInfo = TxInfo
  { txInfoInputs                :: [V2.TxInInfo]
  -- ^ Unchanged
  , txInfoReferenceInputs       :: [V2.TxInInfo]
  -- ^ Unchanged
  , txInfoOutputs               :: [V2.TxOut]
  -- ^ Unchanged
  , txInfoFee                   :: V2.Value
  -- ^ Unchanged
  , txInfoMint                  :: V2.Value
  -- ^ Semantics changed:
  -- In Conway for PlutusV3 translation is different from previous Plutus versions, since we no
  -- longer add a zero ADA value to the mint field during translation.
  -- Fixes: https://github.com/input-output-hk/plutus/issues/5039
  , txInfoTxCerts               :: [TxCert]
  -- ^ Certificate type has changed
  , txInfoWdrl                  :: Map V2.StakingCredential Haskell.Integer
  -- ^ Unchanged
  , txInfoValidRange            :: V2.POSIXTimeRange
  -- ^ Unchanged
  , txInfoSignatories           :: [V2.PubKeyHash]
  -- ^ Unchanged
  , txInfoRedeemers             :: Map ScriptPurpose V2.Redeemer
  -- ^ Semantics changed
  --
  -- ScriptPurpose is now different in Conway
  , txInfoData                  :: Map V2.DatumHash V2.Datum
  -- ^ Unchanged
  , txInfoId                    :: V2.TxId
  -- ^ Unchanged
  , -- New in Conway ===========================================================
    txInfoVotingProcedures      :: Map Voter (Map GovernanceActionId VotingProcedure)
  -- ^ This is Map with all of the votes that were included in the transaction
  , txInfoProposalProcedures    :: [ProposalProcedure]
  -- ^ This is a list with Proposals that will be turned into GovernanceActions, that everyone
  -- can vote on
  , txInfoCurrentTreasuryAmount :: Haskell.Maybe V2.Value
  -- ^ Optional amount for the current treasury. If included it will be checked to be equal
  -- the current amount in the treasury.
  , txInfoTreasuryDonation      :: Haskell.Maybe V2.Value
  -- ^ Optional amount for donating to the current treasury. If included, specified amount
  -- will go into the treasury.
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
      , "Voting Procedures:" <+> pretty txInfoVotingProcedures
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

PlutusTx.makeLift ''ColdCommitteeHash
PlutusTx.makeLift ''HotCommitteeHash
PlutusTx.makeLift ''DRepHash

PlutusTx.makeLift ''DRep
PlutusTx.makeIsDataIndexed
  ''DRep
  [ ('DRepCredential, 0)
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

PlutusTx.makeLift ''Anchor
PlutusTx.makeIsDataIndexed ''Anchor [('Anchor, 0)]

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

PlutusTx.makeLift ''VotingProcedure
PlutusTx.makeIsDataIndexed ''VotingProcedure [('VotingProcedure, 0)]

PlutusTx.makeLift ''Committee
PlutusTx.makeIsDataIndexed ''Committee [('Committee, 0)]

PlutusTx.makeLift ''Constitution
PlutusTx.makeIsDataIndexed ''Constitution [('Constitution, 0)]

PlutusTx.makeLift ''ProtocolVersion
PlutusTx.makeIsDataIndexed ''ProtocolVersion [('ProtocolVersion, 0)]

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
