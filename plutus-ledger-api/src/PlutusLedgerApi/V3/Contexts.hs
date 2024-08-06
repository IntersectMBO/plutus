-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}

module PlutusLedgerApi.V3.Contexts
  ( ColdCommitteeCredential (..)
  , HotCommitteeCredential (..)
  , DRepCredential (..)
  , DRep (..)
  , Delegatee (..)
  , TxCert (..)
  , Voter (..)
  , Vote (..)
  , GovernanceActionId (..)
  , Committee (..)
  , Constitution (..)
  , ProtocolVersion (..)
  , ChangedParameters (..)
  , GovernanceAction (..)
  , ProposalProcedure (..)
  , ScriptPurpose (..)
  , ScriptInfo (..)
  , TxInInfo (..)
  , TxInfo (..)
  , ScriptContext (..)
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

import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3.Tx qualified as V3
import PlutusTx qualified
import PlutusTx.AssocMap hiding (filter, mapMaybe)
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Ratio (Rational)

import Prelude qualified as Haskell

newtype ColdCommitteeCredential = ColdCommitteeCredential V2.Credential
  deriving stock (Generic)
  deriving (Pretty) via (PrettyShow ColdCommitteeCredential)
  deriving newtype
    ( Haskell.Eq
    , Haskell.Ord
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
    , Haskell.Ord
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
    , Haskell.Ord
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
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
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
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
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
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
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
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
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
  { gaidTxId        :: V3.TxId
  , gaidGovActionIx :: Haskell.Integer
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)

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
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)

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
  deriving newtype (Haskell.Show, Haskell.Eq, Haskell.Ord)

instance Pretty Constitution where
  pretty (Constitution script) = "constitutionScript:" <+> pretty script

instance PlutusTx.Eq Constitution where
  {-# INLINEABLE (==) #-}
  Constitution a == Constitution a' = a PlutusTx.== a'

data ProtocolVersion = ProtocolVersion
  { pvMajor :: Haskell.Integer
  , pvMinor :: Haskell.Integer
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)

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
      [ColdCommitteeCredential] -- ^ Committee members to be removed
      (Map ColdCommitteeCredential Haskell.Integer) -- ^ Committee members to be added
      Rational -- ^ New quorum
  | NewConstitution (Haskell.Maybe GovernanceActionId) Constitution
  | InfoAction
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving (Pretty) via (PrettyShow GovernanceAction)

-- | A proposal procedure. The optional anchor is omitted.
data ProposalProcedure = ProposalProcedure
  { ppDeposit          :: V2.Lovelace
  , ppReturnAddr       :: V2.Credential
  , ppGovernanceAction :: GovernanceAction
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)

instance Pretty ProposalProcedure where
  pretty ProposalProcedure{..} =
    vsep
      [ "ppDeposit:" <+> pretty ppDeposit
      , "ppReturnAddr:" <+> pretty ppReturnAddr
      , "ppGovernanceAction:" <+> pretty ppGovernanceAction
      ]

-- | A `ScriptPurpose` uniquely identifies a Plutus script within a transaction.
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
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving (Pretty) via (PrettyShow ScriptPurpose)

-- | Like `ScriptPurpose` but with an optional datum for spending scripts.
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
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving (Pretty) via (PrettyShow ScriptInfo)

-- | An input of a pending transaction.
data TxInInfo = TxInInfo
  { txInInfoOutRef   :: V3.TxOutRef
  , txInInfoResolved :: V2.TxOut
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)

instance PlutusTx.Eq TxInInfo where
  TxInInfo ref res == TxInInfo ref' res' =
    ref PlutusTx.== ref' PlutusTx.&& res PlutusTx.== res'

instance Pretty TxInInfo where
  pretty TxInInfo{txInInfoOutRef, txInInfoResolved} =
    pretty txInInfoOutRef <+> "->" <+> pretty txInInfoResolved

-- | TxInfo for PlutusV3
data TxInfo = TxInfo
  { txInfoInputs                :: [TxInInfo]
  , txInfoReferenceInputs       :: [TxInInfo]
  , txInfoOutputs               :: [V2.TxOut]
  , txInfoFee                   :: V2.Lovelace
  , txInfoMint                  :: V2.Value
  -- ^ The 'Value' minted by this transaction.
  --
  -- /Invariant:/ This field does not contain Ada with zero quantity, unlike
  -- their namesakes in Plutus V1 and V2's ScriptContexts.
  , txInfoTxCerts               :: [TxCert]
  , txInfoWdrl                  :: Map V2.Credential V2.Lovelace
  , txInfoValidRange            :: V2.POSIXTimeRange
  , txInfoSignatories           :: [V2.PubKeyHash]
  , txInfoRedeemers             :: Map ScriptPurpose V2.Redeemer
  , txInfoData                  :: Map V2.DatumHash V2.Datum
  , txInfoId                    :: V3.TxId
  , txInfoVotes                 :: Map Voter (Map GovernanceActionId Vote)
  , txInfoProposalProcedures    :: [ProposalProcedure]
  , txInfoCurrentTreasuryAmount :: Haskell.Maybe V2.Lovelace
  , txInfoTreasuryDonation      :: Haskell.Maybe V2.Lovelace
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

-- | The context that the currently-executing script can access.
data ScriptContext = ScriptContext
  { scriptContextTxInfo     :: TxInfo
  -- ^ information about the transaction the currently-executing script is included in
  , scriptContextRedeemer   :: V2.Redeemer
  -- ^ Redeemer for the currently-executing script
  , scriptContextScriptInfo :: ScriptInfo
  -- ^ the purpose of the currently-executing script, along with information associated
  -- with the purpose
  }
  deriving stock (Generic, Haskell.Eq, Haskell.Show)

instance Pretty ScriptContext where
  pretty ScriptContext{..} =
    vsep
      [ "ScriptInfo:" <+> pretty scriptContextScriptInfo
      , nest 2 (vsep ["TxInfo:", pretty scriptContextTxInfo])
      , nest 2 (vsep ["Redeemer:", pretty scriptContextRedeemer])
      ]

{-# INLINEABLE findOwnInput #-}

-- | Find the input currently being validated.
findOwnInput :: ScriptContext -> Haskell.Maybe TxInInfo
findOwnInput
  ScriptContext
    { scriptContextTxInfo = TxInfo{txInfoInputs}
    , scriptContextScriptInfo = SpendingScript txOutRef _
    } =
    PlutusTx.find
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
  PlutusTx.find
    (\TxInInfo{txInInfoOutRef} -> txInInfoOutRef PlutusTx.== outRef)
    txInfoInputs

{-# INLINEABLE findContinuingOutputs #-}

{- | Find the indices of all the outputs that pay to the same script address we are
currently spending from, if any.
-}
findContinuingOutputs :: ScriptContext -> [Haskell.Integer]
findContinuingOutputs ctx
  | Haskell.Just TxInInfo{txInInfoResolved = V2.TxOut{txOutAddress}} <-
      findOwnInput ctx =
      PlutusTx.findIndices
        (f txOutAddress)
        (txInfoOutputs (scriptContextTxInfo ctx))
  where
    f addr V2.TxOut{txOutAddress = otherAddress} = addr PlutusTx.== otherAddress
findContinuingOutputs _ = PlutusTx.traceError "Le" -- "Can't find any continuing outputs"

{-# INLINEABLE getContinuingOutputs #-}

{- | Get all the outputs that pay to the same script address we are currently spending
from, if any.
-}
getContinuingOutputs :: ScriptContext -> [V2.TxOut]
getContinuingOutputs ctx
  | Haskell.Just TxInInfo{txInInfoResolved = V2.TxOut{txOutAddress}} <-
      findOwnInput ctx =
      PlutusTx.filter (f txOutAddress) (txInfoOutputs (scriptContextTxInfo ctx))
  where
    f addr V2.TxOut{txOutAddress = otherAddress} = addr PlutusTx.== otherAddress
getContinuingOutputs _ = PlutusTx.traceError "Lf" -- "Can't get any continuing outputs"

{-# INLINEABLE txSignedBy #-}

-- | Check if a transaction was signed by the given public key.
txSignedBy :: TxInfo -> V2.PubKeyHash -> Haskell.Bool
txSignedBy TxInfo{txInfoSignatories} k = case PlutusTx.find ((PlutusTx.==) k) txInfoSignatories of
  Haskell.Just _  -> Haskell.True
  Haskell.Nothing -> Haskell.False

{-# INLINEABLE pubKeyOutputsAt #-}

-- | Get the values paid to a public key address by a pending transaction.
pubKeyOutputsAt :: V2.PubKeyHash -> TxInfo -> [V2.Value]
pubKeyOutputsAt pk p =
  let flt V2.TxOut{txOutAddress = V2.Address (V2.PubKeyCredential pk') _, txOutValue}
        | pk PlutusTx.== pk' = Haskell.Just txOutValue
      flt _ = Haskell.Nothing
   in PlutusTx.mapMaybe flt (txInfoOutputs p)

{-# INLINEABLE valuePaidTo #-}

-- | Get the total value paid to a public key address by a pending transaction.
valuePaidTo :: TxInfo -> V2.PubKeyHash -> V2.Value
valuePaidTo ptx pkh = PlutusTx.mconcat (pubKeyOutputsAt pkh ptx)

{-# INLINEABLE valueSpent #-}

-- | Get the total value of inputs spent by this transaction.
valueSpent :: TxInfo -> V2.Value
valueSpent =
  PlutusTx.foldMap (V2.txOutValue PlutusTx.. txInInfoResolved) PlutusTx.. txInfoInputs

{-# INLINEABLE valueProduced #-}

-- | Get the total value of outputs produced by this transaction.
valueProduced :: TxInfo -> V2.Value
valueProduced = PlutusTx.foldMap V2.txOutValue PlutusTx.. txInfoOutputs

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
   in PlutusTx.any spendsOutRef (txInfoInputs txInfo)

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
  , ('TxCertPoolRegister, 7)
  , ('TxCertPoolRetire, 8)
  , ('TxCertAuthHotCommittee, 9)
  , ('TxCertResignColdCommittee, 10)
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
  , ('UpdateCommittee, 4)
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

PlutusTx.makeLift ''ScriptInfo
PlutusTx.makeIsDataIndexed
  ''ScriptInfo
  [ ('MintingScript, 0)
  , ('SpendingScript, 1)
  , ('RewardingScript, 2)
  , ('CertifyingScript, 3)
  , ('VotingScript, 4)
  , ('ProposingScript, 5)
  ]

PlutusTx.makeLift ''TxInInfo
PlutusTx.makeIsDataIndexed ''TxInInfo [('TxInInfo, 0)]

PlutusTx.makeLift ''TxInfo
PlutusTx.makeIsDataIndexed ''TxInfo [('TxInfo, 0)]

PlutusTx.makeLift ''ScriptContext
PlutusTx.makeIsDataIndexed ''ScriptContext [('ScriptContext, 0)]
