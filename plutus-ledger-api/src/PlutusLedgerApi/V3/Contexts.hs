-- editorconfig-checker-disable-file
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
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

import Data.Function ((&))
import Data.Maybe (Maybe (..))
import GHC.Generics (Generic)
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3.MintValue qualified as V3
import PlutusLedgerApi.V3.Tx qualified as V3
import PlutusTx (makeIsDataSchemaIndexed)
import PlutusTx qualified
import PlutusTx.AssocMap (Map, lookup, toList)
import PlutusTx.Blueprint
  ( HasBlueprintDefinition
  , HasBlueprintSchema
  , HasSchemaDefinition
  , Schema (SchemaBuiltInData)
  , SchemaInfo (..)
  , emptySchemaInfo
  )
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition.Derive (definitionRef)
import PlutusTx.Blueprint.Schema (withSchemaInfo)
import PlutusTx.Foldable qualified as F
import PlutusTx.Lift (makeLift)
import PlutusTx.List qualified as List
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Ratio (Rational)
import Prettyprinter (nest, vsep, (<+>))
import Prettyprinter.Extras (Pretty (pretty), PrettyShow (PrettyShow))
import Prelude qualified as Haskell

newtype ColdCommitteeCredential = ColdCommitteeCredential V2.Credential
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)
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

instance
  ( HasSchemaDefinition V2.PubKeyHash referencedTypes
  , HasSchemaDefinition V2.ScriptHash referencedTypes
  )
  => HasBlueprintSchema ColdCommitteeCredential referencedTypes
  where
  schema =
    schema @V2.Credential @referencedTypes
      & withSchemaInfo \info -> info {title = Just "ColdCommitteeCredential"}

newtype HotCommitteeCredential = HotCommitteeCredential V2.Credential
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)
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

instance
  ( HasSchemaDefinition V2.PubKeyHash referencedTypes
  , HasSchemaDefinition V2.ScriptHash referencedTypes
  )
  => HasBlueprintSchema HotCommitteeCredential referencedTypes
  where
  schema =
    schema @V2.Credential
      & withSchemaInfo \info -> info {title = Just "HotCommitteeCredential"}

newtype DRepCredential = DRepCredential V2.Credential
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)
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

instance
  ( HasSchemaDefinition V2.PubKeyHash referencedTypes
  , HasSchemaDefinition V2.ScriptHash referencedTypes
  )
  => HasBlueprintSchema DRepCredential referencedTypes
  where
  schema =
    schema @V2.Credential
      & withSchemaInfo \info -> info {title = Just "DRepCredential"}

data DRep
  = DRep DRepCredential
  | DRepAlwaysAbstain
  | DRepAlwaysNoConfidence
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow DRep)

PlutusTx.deriveEq ''DRep

data Delegatee
  = DelegStake V2.PubKeyHash
  | DelegVote DRep
  | DelegStakeVote V2.PubKeyHash DRep
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow Delegatee)

PlutusTx.deriveEq ''Delegatee

data TxCert
  = -- | Register staking credential with an optional deposit amount
    TxCertRegStaking V2.Credential (Haskell.Maybe V2.Lovelace)
  | -- | Un-Register staking credential with an optional refund amount
    TxCertUnRegStaking V2.Credential (Haskell.Maybe V2.Lovelace)
  | -- | Delegate staking credential to a Delegatee
    TxCertDelegStaking V2.Credential Delegatee
  | {-| Register and delegate staking credential to a Delegatee in one certificate. Note that
    deposit is mandatory. -}
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
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow TxCert)

PlutusTx.deriveEq ''TxCert

data Voter
  = CommitteeVoter HotCommitteeCredential
  | DRepVoter DRepCredential
  | StakePoolVoter V2.PubKeyHash
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow Voter)

PlutusTx.deriveEq ''Voter

-- | A vote. The optional anchor is omitted.
data Vote
  = VoteNo
  | VoteYes
  | Abstain
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow Vote)

PlutusTx.deriveEq ''Vote

-- | Similar to TxOutRef, but for GovActions
data GovernanceActionId = GovernanceActionId
  { gaidTxId :: V3.TxId
  , gaidGovActionIx :: Haskell.Integer
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.deriveEq ''GovernanceActionId

instance Pretty GovernanceActionId where
  pretty GovernanceActionId {..} =
    vsep
      [ "gaidTxId:" <+> pretty gaidTxId
      , "gaidGovActionIx:" <+> pretty gaidGovActionIx
      ]

data Committee = Committee
  { committeeMembers :: Map ColdCommitteeCredential Haskell.Integer
  -- ^ Committee members with epoch number when each of them expires
  , committeeQuorum :: PlutusTx.Rational
  -- ^ Quorum of the committee that is necessary for a successful vote
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)

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
  deriving newtype (Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.deriveEq ''Constitution

instance Pretty Constitution where
  pretty (Constitution script) = "constitutionScript:" <+> pretty script

data ProtocolVersion = ProtocolVersion
  { pvMajor :: Haskell.Integer
  , pvMinor :: Haskell.Integer
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.deriveEq ''ProtocolVersion
PlutusTx.deriveOrd ''ProtocolVersion

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
[conway.cddl](https://github.com/IntersectMBO/cardano-ledger/blob/master/eras/conway/impl/cddl-files/conway.cddl).

/Invariant:/ This map is non-empty, and the keys are stored in ascending order.

This `Data` object has the following format (in pseudocode):

ChangedParametersData = Map ChangedIdData ChangedManyValueData
ChangedIdData = I Integer
ChangedManyValueData =
     ChangedSingleValueData
   | List[ChangedSingleValueData...]
   -- ^ an arbitrary-length, heterogeneous (integer or ratio) list of values (to support sub-parameters)

ChangedSingleValueData =
     I Integer  -- a proposed integer value
   | List[I Integer, I Integer] -- a proposed numerator,denominator (ratio value)
   -- ^ a 2-exact element list; *BE CAREFUL* because this can be alternatively (ambiguously) interpreted
   -- as a many-value data (sub-parameter) of two integer single-value data.

, where Map,I,List are the constructors of `PlutusCore.Data`
and Integer is the usual arbitrary-precision PlutusTx/Haskell Integer. -}
newtype ChangedParameters = ChangedParameters {getChangedParameters :: PlutusTx.BuiltinData}
  deriving stock (Generic, Haskell.Show)
  deriving anyclass (HasBlueprintDefinition)
  deriving newtype
    ( Haskell.Eq
    , Haskell.Ord
    , PlutusTx.Eq
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    , Pretty
    )

instance HasBlueprintSchema ChangedParameters referencedTypes where
  schema = SchemaBuiltInData emptySchemaInfo {title = Just "ChangedParameters"}

data GovernanceAction
  = -- | Hash of the constitution script
    ParameterChange
      (Haskell.Maybe GovernanceActionId)
      ChangedParameters
      (Haskell.Maybe V2.ScriptHash)
  | -- | proposal to update protocol version
    HardForkInitiation (Haskell.Maybe GovernanceActionId) ProtocolVersion
  | -- | Hash of the constitution script
    TreasuryWithdrawals
      (Map V2.Credential V2.Lovelace)
      (Haskell.Maybe V2.ScriptHash)
  | NoConfidence (Haskell.Maybe GovernanceActionId)
  | UpdateCommittee
      (Haskell.Maybe GovernanceActionId)
      [ColdCommitteeCredential]
      -- ^ Committee members to be removed
      (Map ColdCommitteeCredential Haskell.Integer)
      -- ^ Committee members to be added
      Rational
      -- ^ New quorum
  | NewConstitution (Haskell.Maybe GovernanceActionId) Constitution
  | InfoAction
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow GovernanceAction)

-- No PlutusTx.Eq instance, see Note [No PlutusTx.Eq for types with AssocMap]

-- | A proposal procedure. The optional anchor is omitted.
data ProposalProcedure = ProposalProcedure
  { ppDeposit :: V2.Lovelace
  , ppReturnAddr :: V2.Credential
  , ppGovernanceAction :: GovernanceAction
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)

-- No PlutusTx.Eq instance, see Note [No PlutusTx.Eq for types with AssocMap]

instance Pretty ProposalProcedure where
  pretty ProposalProcedure {..} =
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
  deriving anyclass (HasBlueprintDefinition)
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
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow ScriptInfo)

-- | An input of a pending transaction.
data TxInInfo = TxInInfo
  { txInInfoOutRef :: V3.TxOutRef
  , txInInfoResolved :: V2.TxOut
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.deriveEq ''TxInInfo

instance Pretty TxInInfo where
  pretty TxInInfo {txInInfoOutRef, txInInfoResolved} =
    pretty txInInfoOutRef <+> "->" <+> pretty txInInfoResolved

-- | TxInfo for PlutusV3
data TxInfo = TxInfo
  { txInfoInputs :: [TxInInfo]
  , txInfoReferenceInputs :: [TxInInfo]
  , txInfoOutputs :: [V2.TxOut]
  , txInfoFee :: V2.Lovelace
  , txInfoMint :: V3.MintValue
  {-^ The 'Value' minted by this transaction.

  /Invariant:/ This field does not contain Ada with zero quantity, unlike
  their namesakes in Plutus V1 and V2's ScriptContexts. -}
  , txInfoTxCerts :: [TxCert]
  , txInfoWdrl :: Map V2.Credential V2.Lovelace
  , txInfoValidRange :: V2.POSIXTimeRange
  , txInfoSignatories :: [V2.PubKeyHash]
  , txInfoRedeemers :: Map ScriptPurpose V2.Redeemer
  , txInfoData :: Map V2.DatumHash V2.Datum
  , txInfoId :: V3.TxId
  , txInfoVotes :: Map Voter (Map GovernanceActionId Vote)
  , txInfoProposalProcedures :: [ProposalProcedure]
  , txInfoCurrentTreasuryAmount :: Haskell.Maybe V2.Lovelace
  , txInfoTreasuryDonation :: Haskell.Maybe V2.Lovelace
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving anyclass (HasBlueprintDefinition)

-- No PlutusTx.Eq instance, see Note [No PlutusTx.Eq for types with AssocMap]

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

-- | The context that the currently-executing script can access.
data ScriptContext = ScriptContext
  { scriptContextTxInfo :: TxInfo
  -- ^ information about the transaction the currently-executing script is included in
  , scriptContextRedeemer :: V2.Redeemer
  -- ^ Redeemer for the currently-executing script
  , scriptContextScriptInfo :: ScriptInfo
  {-^ the purpose of the currently-executing script, along with information associated
  with the purpose -}
  }
  deriving stock (Generic, Haskell.Eq, Haskell.Show)
  deriving anyclass (HasBlueprintDefinition)

-- No PlutusTx.Eq instance, see Note [No PlutusTx.Eq for types with AssocMap]

instance Pretty ScriptContext where
  pretty ScriptContext {..} =
    vsep
      [ "ScriptInfo:" <+> pretty scriptContextScriptInfo
      , nest 2 (vsep ["TxInfo:", pretty scriptContextTxInfo])
      , nest 2 (vsep ["Redeemer:", pretty scriptContextRedeemer])
      ]

-- | Find the input currently being validated.
findOwnInput :: ScriptContext -> Haskell.Maybe TxInInfo
findOwnInput
  ScriptContext
    { scriptContextTxInfo = TxInfo {txInfoInputs}
    , scriptContextScriptInfo = SpendingScript txOutRef _
    } =
    List.find
      (\TxInInfo {txInInfoOutRef} -> txInInfoOutRef PlutusTx.== txOutRef)
      txInfoInputs
findOwnInput _ = Haskell.Nothing
{-# INLINEABLE findOwnInput #-}

-- | Find the data corresponding to a data hash, if there is one
findDatum :: V2.DatumHash -> TxInfo -> Haskell.Maybe V2.Datum
findDatum dsh TxInfo {txInfoData} = lookup dsh txInfoData
{-# INLINEABLE findDatum #-}

{-| Find the hash of a datum, if it is part of the pending transaction's
hashes -}
findDatumHash :: V2.Datum -> TxInfo -> Haskell.Maybe V2.DatumHash
findDatumHash ds TxInfo {txInfoData} =
  PlutusTx.fst PlutusTx.<$> List.find f (toList txInfoData)
  where
    f (_, ds') = ds' PlutusTx.== ds
{-# INLINEABLE findDatumHash #-}

{-| Given a UTXO reference and a transaction (`TxInfo`), resolve it to one of the
transaction's inputs (`TxInInfo`).

Note: this only searches the true transaction inputs and not the referenced transaction inputs. -}
findTxInByTxOutRef :: V3.TxOutRef -> TxInfo -> Haskell.Maybe TxInInfo
findTxInByTxOutRef outRef TxInfo {txInfoInputs} =
  List.find
    (\TxInInfo {txInInfoOutRef} -> txInInfoOutRef PlutusTx.== outRef)
    txInfoInputs
{-# INLINEABLE findTxInByTxOutRef #-}

{-| Find the indices of all the outputs that pay to the same script address we are
currently spending from, if any. -}
findContinuingOutputs :: ScriptContext -> [Haskell.Integer]
findContinuingOutputs ctx
  | Haskell.Just TxInInfo {txInInfoResolved = V2.TxOut {txOutAddress}} <-
      findOwnInput ctx =
      List.findIndices
        (f txOutAddress)
        (txInfoOutputs (scriptContextTxInfo ctx))
  where
    f addr V2.TxOut {txOutAddress = otherAddress} = addr PlutusTx.== otherAddress
findContinuingOutputs _ = PlutusTx.traceError "Le" -- "Can't find any continuing outputs"
{-# INLINEABLE findContinuingOutputs #-}

{-| Get all the outputs that pay to the same script address we are currently spending
from, if any. -}
getContinuingOutputs :: ScriptContext -> [V2.TxOut]
getContinuingOutputs ctx
  | Haskell.Just TxInInfo {txInInfoResolved = V2.TxOut {txOutAddress}} <-
      findOwnInput ctx =
      List.filter (f txOutAddress) (txInfoOutputs (scriptContextTxInfo ctx))
  where
    f addr V2.TxOut {txOutAddress = otherAddress} = addr PlutusTx.== otherAddress
getContinuingOutputs _ = PlutusTx.traceError "Lf" -- "Can't get any continuing outputs"
{-# INLINEABLE getContinuingOutputs #-}

-- | Check if a transaction was signed by the given public key.
txSignedBy :: TxInfo -> V2.PubKeyHash -> Haskell.Bool
txSignedBy TxInfo {txInfoSignatories} k = case List.find ((PlutusTx.==) k) txInfoSignatories of
  Haskell.Just _ -> Haskell.True
  Haskell.Nothing -> Haskell.False
{-# INLINEABLE txSignedBy #-}

-- | Get the values paid to a public key address by a pending transaction.
pubKeyOutputsAt :: V2.PubKeyHash -> TxInfo -> [V2.Value]
pubKeyOutputsAt pk p =
  let flt V2.TxOut {txOutAddress = V2.Address (V2.PubKeyCredential pk') _, txOutValue}
        | pk PlutusTx.== pk' = Haskell.Just txOutValue
      flt _ = Haskell.Nothing
   in PlutusTx.mapMaybe flt (txInfoOutputs p)
{-# INLINEABLE pubKeyOutputsAt #-}

-- | Get the total value paid to a public key address by a pending transaction.
valuePaidTo :: TxInfo -> V2.PubKeyHash -> V2.Value
valuePaidTo ptx pkh = PlutusTx.mconcat (pubKeyOutputsAt pkh ptx)
{-# INLINEABLE valuePaidTo #-}

-- | Get the total value of inputs spent by this transaction.
valueSpent :: TxInfo -> V2.Value
valueSpent =
  F.foldMap (V2.txOutValue PlutusTx.. txInInfoResolved) PlutusTx.. txInfoInputs
{-# INLINEABLE valueSpent #-}

-- | Get the total value of outputs produced by this transaction.
valueProduced :: TxInfo -> V2.Value
valueProduced = F.foldMap V2.txOutValue PlutusTx.. txInfoOutputs
{-# INLINEABLE valueProduced #-}

-- | The 'CurrencySymbol' of the current validator script.
ownCurrencySymbol :: ScriptContext -> V2.CurrencySymbol
ownCurrencySymbol ScriptContext {scriptContextScriptInfo = MintingScript cs} = cs
ownCurrencySymbol _ =
  -- "Can't get currency symbol of the current validator script"
  PlutusTx.traceError "Lh"
{-# INLINEABLE ownCurrencySymbol #-}

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
   in List.any spendsOutRef (txInfoInputs txInfo)
{-# INLINEABLE spendsOutput #-}

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(makeLift ''ColdCommitteeCredential)
$(makeLift ''HotCommitteeCredential)
$(makeLift ''DRepCredential)

$(makeLift ''DRep)
$( makeIsDataSchemaIndexed
     ''DRep
     [ ('DRep, 0)
     , ('DRepAlwaysAbstain, 1)
     , ('DRepAlwaysNoConfidence, 2)
     ]
 )

$(makeLift ''Delegatee)
$( makeIsDataSchemaIndexed
     ''Delegatee
     [ ('DelegStake, 0)
     , ('DelegVote, 1)
     , ('DelegStakeVote, 2)
     ]
 )

$(makeLift ''TxCert)
$( makeIsDataSchemaIndexed
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
 )

$(makeLift ''Voter)
$( makeIsDataSchemaIndexed
     ''Voter
     [ ('CommitteeVoter, 0)
     , ('DRepVoter, 1)
     , ('StakePoolVoter, 2)
     ]
 )

$(makeLift ''Vote)
$( makeIsDataSchemaIndexed
     ''Vote
     [ ('VoteNo, 0)
     , ('VoteYes, 1)
     , ('Abstain, 2)
     ]
 )

$(makeLift ''GovernanceActionId)
$(makeIsDataSchemaIndexed ''GovernanceActionId [('GovernanceActionId, 0)])

$(makeLift ''Committee)
$(makeIsDataSchemaIndexed ''Committee [('Committee, 0)])

$(makeLift ''Constitution)
$(makeIsDataSchemaIndexed ''Constitution [('Constitution, 0)])

$(makeLift ''ProtocolVersion)
$(makeIsDataSchemaIndexed ''ProtocolVersion [('ProtocolVersion, 0)])

$(makeLift ''ChangedParameters)
$(makeLift ''GovernanceAction)
$( makeIsDataSchemaIndexed
     ''GovernanceAction
     [ ('ParameterChange, 0)
     , ('HardForkInitiation, 1)
     , ('TreasuryWithdrawals, 2)
     , ('NoConfidence, 3)
     , ('UpdateCommittee, 4)
     , ('NewConstitution, 5)
     , ('InfoAction, 6)
     ]
 )

$(makeLift ''ProposalProcedure)
$(makeIsDataSchemaIndexed ''ProposalProcedure [('ProposalProcedure, 0)])

$(makeLift ''ScriptPurpose)
$( makeIsDataSchemaIndexed
     ''ScriptPurpose
     [ ('Minting, 0)
     , ('Spending, 1)
     , ('Rewarding, 2)
     , ('Certifying, 3)
     , ('Voting, 4)
     , ('Proposing, 5)
     ]
 )

$(makeLift ''ScriptInfo)
$( makeIsDataSchemaIndexed
     ''ScriptInfo
     [ ('MintingScript, 0)
     , ('SpendingScript, 1)
     , ('RewardingScript, 2)
     , ('CertifyingScript, 3)
     , ('VotingScript, 4)
     , ('ProposingScript, 5)
     ]
 )

----------------------------------------------------------------------------------------------------
-- TH Splices --------------------------------------------------------------------------------------

$(makeLift ''TxInInfo)
$(makeIsDataSchemaIndexed ''TxInInfo [('TxInInfo, 0)])

$(makeLift ''TxInfo)
$(makeIsDataSchemaIndexed ''TxInfo [('TxInfo, 0)])

$(makeLift ''ScriptContext)
$(makeIsDataSchemaIndexed ''ScriptContext [('ScriptContext, 0)])
