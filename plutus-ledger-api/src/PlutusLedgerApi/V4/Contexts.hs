-- editorconfig-checker-disable-file
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}

module PlutusLedgerApi.V4.Contexts
  ( AccountId (..)
  , AccountBalanceInterval (..)
  , AccountBalanceIntervals (..)
  , ColdCommitteeCredential (..)
  , HotCommitteeCredential (..)
  , DRepCredential (..)
  , DRep (..)
  , Delegatee (..)
  , TxCert (..)
  , Voter (..)
  , Vote (..)
  , GovernanceActionId (GovernanceActionId, gaidTxId, gaidGovActionIx)
  , Committee (Committee, committeeMembers, committeeQuorum)
  , Constitution (..)
  , ProtocolVersion (ProtocolVersion, pvMajor, pvMinor)
  , ChangedParameters (..)
  , GovernanceAction (..)
  , ProposalProcedure (ProposalProcedure, ppDeposit, ppReturnAddr, ppGovernanceAction)
  , ScriptPurpose (..)
  , ScriptInfo (..)
  , TxInInfo (..)
  , TxInfo (..)
  , TopTxInfoSimplified (..)
  , TopTxInfo (..)
  , ScriptContext (..)
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

import Data.Function ((&))
import GHC.Generics (Generic)
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3.Contexts
  ( ChangedParameters (..)
  , ColdCommitteeCredential (..)
  , DRep (..)
  , DRepCredential (..)
  , Delegatee (..)
  , HotCommitteeCredential (..)
  , Vote (..)
  , Voter (..)
  )
import PlutusLedgerApi.V3.Contexts qualified as V3
import PlutusLedgerApi.V3.MintValue qualified as V3
import PlutusLedgerApi.V3.Tx qualified as V3
import PlutusLedgerApi.V4.Address (AccountId (..), Address (..))
import PlutusLedgerApi.V4.Internal (ListEncoded (..))
import PlutusLedgerApi.V4.Ratio (Rational)
import PlutusLedgerApi.V4.Time (POSIXTimeRange)
import PlutusLedgerApi.V4.Tx (TxOut (..), TxOutRef (..))
import PlutusTx (makeIsDataSchemaAsList, makeIsDataSchemaIndexed)
import PlutusTx qualified
import PlutusTx.AssocMap (Map, lookup, toList)
import PlutusTx.Blueprint
  ( HasBlueprintSchema
  , SchemaInfo (..)
  )
import PlutusTx.Blueprint.Class (HasBlueprintSchema (..))
import PlutusTx.Blueprint.Definition (HasBlueprintDefinition (..), UnrollAll)
import PlutusTx.Blueprint.Definition.Derive (definitionRef)
import PlutusTx.Blueprint.Schema (withSchemaInfo)
import PlutusTx.Foldable qualified as F
import PlutusTx.Lift (makeLift)
import PlutusTx.List qualified as List
import PlutusTx.Prelude qualified as PlutusTx
import Prettyprinter (nest, vsep, (<+>))
import Prettyprinter.Extras (Pretty (pretty), PrettyShow (PrettyShow))
import Prelude qualified as Haskell

newtype GovernanceActionId = GovernanceActionIdValue V3.GovernanceActionId
  deriving stock (Generic)
  deriving newtype (Haskell.Show, Haskell.Eq, Haskell.Ord, Pretty, PlutusTx.Eq)
  deriving
    (PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    via ListEncoded V3.GovernanceActionId

pattern GovernanceActionId :: V3.TxId -> Haskell.Integer -> GovernanceActionId
pattern GovernanceActionId {gaidTxId, gaidGovActionIx} =
  GovernanceActionIdValue (V3.GovernanceActionId gaidTxId gaidGovActionIx)
{-# COMPLETE GovernanceActionId #-}

instance HasBlueprintDefinition GovernanceActionId where
  type Unroll GovernanceActionId = GovernanceActionId ': UnrollAll '[V3.TxId, Haskell.Integer]

instance
  HasBlueprintSchema V3.GovernanceActionId referencedTypes
  => HasBlueprintSchema GovernanceActionId referencedTypes
  where
  schema = schema @(ListEncoded V3.GovernanceActionId) @referencedTypes

PlutusTx.makeLift ''GovernanceActionId

newtype ProtocolVersion = ProtocolVersionValue V3.ProtocolVersion
  deriving stock (Generic)
  deriving newtype (Haskell.Show, Haskell.Eq, Haskell.Ord, Pretty, PlutusTx.Eq, PlutusTx.Ord)
  deriving
    (PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    via ListEncoded V3.ProtocolVersion

pattern ProtocolVersion :: Haskell.Integer -> Haskell.Integer -> ProtocolVersion
pattern ProtocolVersion {pvMajor, pvMinor} = ProtocolVersionValue (V3.ProtocolVersion pvMajor pvMinor)
{-# COMPLETE ProtocolVersion #-}

instance HasBlueprintDefinition ProtocolVersion where
  type Unroll ProtocolVersion = '[ProtocolVersion, Haskell.Integer]

instance
  HasBlueprintSchema V3.ProtocolVersion referencedTypes
  => HasBlueprintSchema ProtocolVersion referencedTypes
  where
  schema = schema @(ListEncoded V3.ProtocolVersion) @referencedTypes

PlutusTx.makeLift ''ProtocolVersion

newtype Constitution = Constitution {constitutionScript :: Haskell.Maybe V2.ScriptHash}
  deriving stock (Generic)
  deriving newtype (Haskell.Show, Haskell.Eq, Haskell.Ord, PlutusTx.Eq)
  deriving anyclass (HasBlueprintDefinition)
  deriving
    (PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    via ListEncoded V3.Constitution

instance
  HasBlueprintSchema V3.Constitution referencedTypes
  => HasBlueprintSchema Constitution referencedTypes
  where
  schema = schema @(ListEncoded V3.Constitution) @referencedTypes

instance Pretty Constitution where
  pretty (Constitution script) = "constitutionScript:" <+> pretty script

PlutusTx.makeLift ''Constitution

newtype Committee = CommitteeValue (Map ColdCommitteeCredential Haskell.Integer, Rational)
  deriving stock (Generic)
  deriving newtype (Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving
    (PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    via ListEncoded (Map ColdCommitteeCredential Haskell.Integer, Rational)

pattern Committee :: Map ColdCommitteeCredential Haskell.Integer -> Rational -> Committee
pattern Committee {committeeMembers, committeeQuorum} = CommitteeValue (committeeMembers, committeeQuorum)
{-# COMPLETE Committee #-}

instance HasBlueprintDefinition Committee where
  type
    Unroll Committee =
      Committee ': UnrollAll '[Map ColdCommitteeCredential Haskell.Integer, Rational]

instance
  HasBlueprintSchema (Map ColdCommitteeCredential Haskell.Integer, Rational) referencedTypes
  => HasBlueprintSchema Committee referencedTypes
  where
  schema = schema @(ListEncoded (Map ColdCommitteeCredential Haskell.Integer, Rational)) @referencedTypes

instance Pretty Committee where
  pretty Committee {..} =
    vsep
      ["committeeMembers:" <+> pretty committeeMembers, "committeeQuorum:" <+> pretty committeeQuorum]

PlutusTx.makeLift ''Committee

data GovernanceAction
  = ParameterChange (Haskell.Maybe GovernanceActionId) ChangedParameters (Haskell.Maybe V2.ScriptHash)
  | HardForkInitiation (Haskell.Maybe GovernanceActionId) ProtocolVersion
  | TreasuryWithdrawals (Map V2.Credential V2.Lovelace) (Haskell.Maybe V2.ScriptHash)
  | NoConfidence (Haskell.Maybe GovernanceActionId)
  | UpdateCommittee
      (Haskell.Maybe GovernanceActionId)
      [ColdCommitteeCredential]
      (Map ColdCommitteeCredential Haskell.Integer)
      Rational
  | NewConstitution (Haskell.Maybe GovernanceActionId) Constitution
  | InfoAction
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow GovernanceAction)

PlutusTx.makeLift ''GovernanceAction
PlutusTx.makeIsDataSchemaIndexed
  ''GovernanceAction
  [ ('ParameterChange, 0)
  , ('HardForkInitiation, 1)
  , ('TreasuryWithdrawals, 2)
  , ('NoConfidence, 3)
  , ('UpdateCommittee, 4)
  , ('NewConstitution, 5)
  , ('InfoAction, 6)
  ]

newtype ProposalProcedure = ProposalProcedureValue (V2.Lovelace, V2.Credential, GovernanceAction)
  deriving stock (Generic)
  deriving newtype (Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving
    (PlutusTx.ToData, PlutusTx.FromData, PlutusTx.UnsafeFromData)
    via ListEncoded (V2.Lovelace, V2.Credential, GovernanceAction)

pattern ProposalProcedure :: V2.Lovelace -> V2.Credential -> GovernanceAction -> ProposalProcedure
pattern ProposalProcedure {ppDeposit, ppReturnAddr, ppGovernanceAction} =
  ProposalProcedureValue (ppDeposit, ppReturnAddr, ppGovernanceAction)
{-# COMPLETE ProposalProcedure #-}

instance HasBlueprintDefinition ProposalProcedure where
  type
    Unroll ProposalProcedure =
      ProposalProcedure ': UnrollAll '[V2.Lovelace, V2.Credential, GovernanceAction]

instance
  HasBlueprintSchema (V2.Lovelace, V2.Credential, GovernanceAction) referencedTypes
  => HasBlueprintSchema ProposalProcedure referencedTypes
  where
  schema = schema @(ListEncoded (V2.Lovelace, V2.Credential, GovernanceAction)) @referencedTypes

instance Pretty ProposalProcedure where
  pretty ProposalProcedure {..} =
    vsep
      [ "ppDeposit:" <+> pretty ppDeposit
      , "ppReturnAddr:" <+> pretty ppReturnAddr
      , "ppGovernanceAction:" <+> pretty ppGovernanceAction
      ]

PlutusTx.makeLift ''ProposalProcedure

data AccountBalanceInterval
  = AccountBalanceLowerBound V2.Lovelace
  | AccountBalanceUpperBound V2.Lovelace
  | AccountBalanceBothBounds V2.Lovelace V2.Lovelace
  | AccountBalanceExact V2.Lovelace
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow AccountBalanceInterval)

PlutusTx.deriveEq ''AccountBalanceInterval

$(makeLift ''AccountBalanceInterval)
$( makeIsDataSchemaIndexed
     ''AccountBalanceInterval
     [ ('AccountBalanceLowerBound, 0)
     , ('AccountBalanceUpperBound, 1)
     , ('AccountBalanceBothBounds, 2)
     , ('AccountBalanceExact, 3)
     ]
 )

newtype AccountBalanceIntervals = AccountBalanceIntervals (Map AccountId AccountBalanceInterval)
  deriving stock (Generic)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow AccountBalanceIntervals)
  deriving newtype
    ( Haskell.Eq
    , Haskell.Ord
    , Haskell.Show
    , PlutusTx.ToData
    , PlutusTx.FromData
    , PlutusTx.UnsafeFromData
    )

instance
  ( HasBlueprintSchema AccountId referencedTypes
  , HasBlueprintSchema AccountBalanceInterval referencedTypes
  )
  => HasBlueprintSchema AccountBalanceIntervals referencedTypes
  where
  schema =
    schema @(Map AccountId AccountBalanceInterval) @referencedTypes
      & withSchemaInfo \info -> info {title = Haskell.Just "AccountBalanceIntervals"}

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
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow TxCert)

PlutusTx.deriveEq ''TxCert

data ScriptPurpose
  = Minting V2.ScriptHash V2.CurrencySymbol
  | Spending V2.ScriptHash TxOutRef
  | Withdrawing V2.ScriptHash V2.Credential
  | Certifying V2.ScriptHash Haskell.Integer TxCert
  | Voting V2.ScriptHash Voter
  | Proposing V2.ScriptHash Haskell.Integer ProposalProcedure
  | Guarding V2.ScriptHash Haskell.Integer
  deriving stock (Generic, Haskell.Show, Haskell.Eq, Haskell.Ord)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow ScriptPurpose)

-- | An input of a pending transaction.
data TxInInfo = TxInInfo
  { txInInfoOutRef :: TxOutRef
  , txInInfoResolved :: TxOut
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving anyclass (HasBlueprintDefinition)

PlutusTx.deriveEq ''TxInInfo

instance Pretty TxInInfo where
  pretty TxInInfo {txInInfoOutRef, txInInfoResolved} =
    pretty txInInfoOutRef <+> "->" <+> pretty txInInfoResolved

data TxInfo = TxInfo
  { txInfoId :: V3.TxId
  , txInfoSubTxIx :: Haskell.Maybe Haskell.Integer
  , txInfoInputs :: [TxInInfo]
  , txInfoReferenceInputs :: [TxInInfo]
  , txInfoOutputs :: [TxOut]
  , txInfoMint :: V3.MintValue
  , txInfoTxCerts :: [TxCert]
  , txInfoWithdrawals :: Map V2.Credential V2.Lovelace
  , txInfoDirectDeposits :: Map V2.Credential V2.Lovelace
  , txInfoAccountBalanceIntervals :: AccountBalanceIntervals
  , txInfoValidRange :: POSIXTimeRange
  , txInfoGuards :: [V2.Credential]
  , txInfoRequiredTopLevelGuards :: Map V2.Credential (Haskell.Maybe V2.Datum)
  , txInfoRedeemers :: Map ScriptPurpose V2.Redeemer
  , txInfoData :: Map V2.DatumHash V2.Datum
  , txInfoVotes :: Map Voter (Map GovernanceActionId Vote)
  , txInfoProposalProcedures :: [ProposalProcedure]
  , txInfoCurrentTreasuryAmount :: Haskell.Maybe V2.Lovelace
  , txInfoTreasuryDonation :: V2.Lovelace
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving anyclass (HasBlueprintDefinition)

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

data TopTxInfoSimplified = TopTxInfoSimplified
  { ttisIds :: [V3.TxId]
  {-^ List of all `TxId`s fro the whole transaction, including the top-level transaction, which is
  always going to be the last one in the list. -}
  , ttisInputs :: [TxInInfo]
  -- ^ Concatenated list of all `txInfoInputs`'
  , ttisReferenceInputs :: [TxInInfo]
  -- ^ Concatenated list of all `txInfoReferenceInputs`'
  , ttisOutputs :: [TxOut]
  -- ^ Concatenated list of all `txInfoOutputs`'
  , ttisMints :: V3.MintValue
  -- ^ `MintValue`s from all `txInfoMint` with positive amounts
  , ttisBurns :: V3.MintValue
  -- ^ `MintValue`s from all `txInfoMint` with negative amounts
  , ttisTxCerts :: [TxCert]
  {-^ Concatenated list of all `ttisTxCerts`'. Note, that unlike individual lists in each
  `txInfoTxCerts`, this one can contain duplicates. -}
  , ttisWithdrawals :: Map V2.Credential V2.Lovelace
  -- ^ Union of all `txInfoWithdrawals` with a sum on the range for duplicate credentials
  , ttisDirectDeposits :: Map V2.Credential V2.Lovelace
  -- ^ Union of all `txInfoWithdrawals` with a sum on the range for duplicate credentials
  , ttisValidRange :: POSIXTimeRange
  -- ^ Intersection of all validity intervals from within the whole transaction
  , ttisGuards :: [V2.Credential]
  -- ^ Concatenated list of all `txInfoGuards`'
  , ttisRequiredTopLevelGuards :: [V2.Credential]
  {-^ Deduplicated set of required top level guards. It is impossible to keep the range of the Map
  due to potential presence of duplicates in the domain between different sub-transactions,
  therefore the range is eliminated. -}
  , ttisScriptPurposes :: [ScriptPurpose]
  {-^ Union of all of the `Redeemer`s. Note that it is not possible to preserve actual `Redeemer`s
  upon `union` operation due to potential duplicates in the domain. Therefore it is collapsed to
  a Set of `ScriptPurpose`s only with duplicates removed. -}
  , ttisData :: Map V2.DatumHash V2.Datum
  {-^ Union of all `txInfoData`. Duplicates are simply removed, since domain and range are
  a one-to-one mapping. -}
  , ttisVotes :: Map Voter (Map GovernanceActionId Vote)
  {-^ Union of all of the votes. Note that a vote in a sub-sequent sub-transaction or a top level
  transaction can replace a vote from a prior sub-transaction. -}
  , ttisProposalProcedures :: [ProposalProcedure]
  -- ^ Concatenated list of all `ProposalPrecedure`s.
  , ttisCurrentTreasuryAmount :: Haskell.Maybe V2.Lovelace
  {-^ Value of the treasury, which will be present if any of sub-transactions or top level
  transaction included such value -}
  , ttisTreasuryDonations :: V2.Lovelace
  -- ^ Sum of all `txInfoTreasuryDonation`s
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow TopTxInfoSimplified)

data TopTxInfo = TopTxInfo
  { topTxInfoSubTransactions :: [TxInfo]
  {-^ List of `TxInfo`s for all sub-transactions. Not that `TxInfo` for the top level transaction
  itslef is not present in this list. -}
  , topTxInfoDatums :: Map V3.TxId V2.Datum
  {-^ Datums supplied in `requiredTopLevelGuards` for that script. Plutus scripts require a datum
  to be supplied when listed `requiredTopLevelGuards`. That `Map` will be empty if none of the
  transactions within the whole transaction require Plutus scripts to be present in `Guards` -}
  , topTxInfoStartingAccountBalanceIntervals :: AccountBalanceIntervals
  {-^ This is a field that allows top level transaction to specify the balance intervals before
  the whole transaction is applied -}
  , topTxInfoSimplified :: TopTxInfoSimplified
  {-^ Aggregated view on the whole transaction, namely information about sub-transactions and the
  top level transaction all concatenated together with loss of some information -}
  }
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow TopTxInfo)

data ScriptInfo
  = MintingScript V2.CurrencySymbol
  | SpendingScript TxOutRef (Haskell.Maybe V2.Datum)
  | WithdrawingScript AccountId
  | CertifyingScript
      Haskell.Integer
      -- ^ 0-based index of the given `TxCert` in `txInfoTxCerts`
      TxCert
  | VotingScript Voter
  | ProposingScript
      Haskell.Integer
      -- ^ 0-based index of the given `ProposalProcedure` in `txInfoProposalProcedures`
      ProposalProcedure
  | {-| Whenever a `Guard` is executed at the top transaction level it will include extra
    information about potential sub-transactions. In other words for sub-transactions this is
    guaranteed to be `Nothing`, while for top level transactions this is guaranteed to be
    `Just` -}
    GuardingScript
      Haskell.Integer
      (Haskell.Maybe TopTxInfo)
  deriving stock (Generic, Haskell.Show, Haskell.Eq)
  deriving anyclass (HasBlueprintDefinition)
  deriving (Pretty) via (PrettyShow ScriptInfo)

data ScriptContext = ScriptContext
  { scriptContextTxInfo :: TxInfo
  -- ^ Information about the transaction the currently-executing script is included in
  , scriptContextRedeemer :: V2.Redeemer
  -- ^ Redeemer for the currently-executing script
  , scriptContextScriptInfo :: ScriptInfo
  {-^ the purpose of the currently-executing script, along with information associated
  with the purpose -}
  , scriptContextScriptHash :: V2.ScriptHash
  -- ^ Hash of the script that is being executed
  }
  deriving stock (Generic, Haskell.Eq, Haskell.Show)
  deriving anyclass (HasBlueprintDefinition)

instance Pretty ScriptContext where
  pretty ScriptContext {..} =
    vsep
      [ "ScriptInfo:" <+> pretty scriptContextScriptInfo
      , "ScriptHash:" <+> pretty scriptContextScriptHash
      , nest 2 (vsep ["TxInfo:", pretty scriptContextTxInfo])
      , nest 2 (vsep ["Redeemer:", pretty scriptContextRedeemer])
      ]

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

findDatum :: V2.DatumHash -> TxInfo -> Haskell.Maybe V2.Datum
findDatum dsh TxInfo {txInfoData} = lookup dsh txInfoData
{-# INLINEABLE findDatum #-}

findDatumHash :: V2.Datum -> TxInfo -> Haskell.Maybe V2.DatumHash
findDatumHash ds TxInfo {txInfoData} =
  PlutusTx.fst PlutusTx.<$> List.find (\(_, ds') -> ds' PlutusTx.== ds) (toList txInfoData)
{-# INLINEABLE findDatumHash #-}

findTxInByTxOutRef :: TxOutRef -> TxInfo -> Haskell.Maybe TxInInfo
findTxInByTxOutRef outRef TxInfo {txInfoInputs} =
  List.find
    (\TxInInfo {txInInfoOutRef} -> txInInfoOutRef PlutusTx.== outRef)
    txInfoInputs
{-# INLINEABLE findTxInByTxOutRef #-}

{-| Find the indices of outputs in the current sub-transaction or top-level transaction
that pay to the same script address we are currently spending from. This does not search
the outputs of the whole transaction. -}
findContinuingOutputs :: ScriptContext -> [Haskell.Integer]
findContinuingOutputs ctx
  | Haskell.Just TxInInfo {txInInfoResolved = TxOut {txOutAddress}} <- findOwnInput ctx =
      List.findIndices
        (\TxOut {txOutAddress = otherAddress} -> txOutAddress PlutusTx.== otherAddress)
        (txInfoOutputs (scriptContextTxInfo ctx))
findContinuingOutputs _ = PlutusTx.traceError "Le"
{-# INLINEABLE findContinuingOutputs #-}

{-| Get the outputs in the current sub-transaction or top-level transaction that pay to
the same script address we are currently spending from. This does not search the outputs
of the whole transaction. -}
getContinuingOutputs :: ScriptContext -> [TxOut]
getContinuingOutputs ctx
  | Haskell.Just TxInInfo {txInInfoResolved = TxOut {txOutAddress}} <- findOwnInput ctx =
      List.filter
        (\TxOut {txOutAddress = otherAddress} -> txOutAddress PlutusTx.== otherAddress)
        (txInfoOutputs (scriptContextTxInfo ctx))
getContinuingOutputs _ = PlutusTx.traceError "Lf"
{-# INLINEABLE getContinuingOutputs #-}

txSignedBy :: TxInfo -> V2.PubKeyHash -> Haskell.Bool
txSignedBy TxInfo {txInfoGuards} keyHash =
  List.any ((PlutusTx.==) (V2.PubKeyCredential keyHash)) txInfoGuards
{-# INLINEABLE txSignedBy #-}

pubKeyOutputsAt :: V2.PubKeyHash -> TxInfo -> [V2.Value]
pubKeyOutputsAt pk txInfo =
  let atPubKey TxOut {txOutAddress = Address (V2.PubKeyCredential pk') _, txOutValue}
        | pk PlutusTx.== pk' = Haskell.Just txOutValue
      atPubKey _ = Haskell.Nothing
   in PlutusTx.mapMaybe atPubKey (txInfoOutputs txInfo)
{-# INLINEABLE pubKeyOutputsAt #-}

valuePaidTo :: TxInfo -> V2.PubKeyHash -> V2.Value
valuePaidTo txInfo keyHash = PlutusTx.mconcat (pubKeyOutputsAt keyHash txInfo)
{-# INLINEABLE valuePaidTo #-}

valueSpent :: TxInfo -> V2.Value
valueSpent = F.foldMap (txOutValue PlutusTx.. txInInfoResolved) PlutusTx.. txInfoInputs
{-# INLINEABLE valueSpent #-}

valueProduced :: TxInfo -> V2.Value
valueProduced = F.foldMap txOutValue PlutusTx.. txInfoOutputs
{-# INLINEABLE valueProduced #-}

ownCurrencySymbol :: ScriptContext -> V2.CurrencySymbol
ownCurrencySymbol ScriptContext {scriptContextScriptInfo = MintingScript currencySymbol} = currencySymbol
ownCurrencySymbol _ = PlutusTx.traceError "Lh"
{-# INLINEABLE ownCurrencySymbol #-}

spendsOutput :: TxInfo -> V3.TxId -> Haskell.Integer -> Haskell.Bool
spendsOutput txInfo txId outputIndex =
  List.any
    ( \TxInInfo {txInInfoOutRef = TxOutRef refId refIndex} ->
        txId PlutusTx.== refId PlutusTx.&& outputIndex PlutusTx.== refIndex
    )
    (txInfoInputs txInfo)
{-# INLINEABLE spendsOutput #-}

$(makeLift ''AccountBalanceIntervals)

$(makeLift ''TxCert)
$( makeIsDataSchemaIndexed
     ''TxCert
     [ ('TxCertRegAccount, 0)
     , ('TxCertUnRegAccount, 1)
     , ('TxCertDelegAccount, 2)
     , ('TxCertRegAccountDeleg, 3)
     , ('TxCertRegDRep, 4)
     , ('TxCertUpdateDRep, 5)
     , ('TxCertUnRegDRep, 6)
     , ('TxCertPoolRegister, 7)
     , ('TxCertPoolRetire, 8)
     , ('TxCertAuthHotCommittee, 9)
     , ('TxCertResignColdCommittee, 10)
     ]
 )

$(makeLift ''ScriptPurpose)
$( makeIsDataSchemaIndexed
     ''ScriptPurpose
     [ ('Minting, 0)
     , ('Spending, 1)
     , ('Withdrawing, 2)
     , ('Certifying, 3)
     , ('Voting, 4)
     , ('Proposing, 5)
     , ('Guarding, 6)
     ]
 )

$(makeLift ''TxInInfo)
$(makeIsDataSchemaAsList ''TxInInfo)

$(makeLift ''TxInfo)
$(makeIsDataSchemaAsList ''TxInfo)

$(makeLift ''TopTxInfoSimplified)
$(makeIsDataSchemaAsList ''TopTxInfoSimplified)

$(makeLift ''TopTxInfo)
$(makeIsDataSchemaAsList ''TopTxInfo)

$(makeLift ''ScriptInfo)
$( makeIsDataSchemaIndexed
     ''ScriptInfo
     [ ('MintingScript, 0)
     , ('SpendingScript, 1)
     , ('WithdrawingScript, 2)
     , ('CertifyingScript, 3)
     , ('VotingScript, 4)
     , ('ProposingScript, 5)
     , ('GuardingScript, 6)
     ]
 )

$(makeLift ''ScriptContext)
$(makeIsDataSchemaAsList ''ScriptContext)
