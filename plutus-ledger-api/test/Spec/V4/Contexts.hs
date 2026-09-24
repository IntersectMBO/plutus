{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}

{-| Parity tests between the helper functions in "PlutusLedgerApi.V4.Contexts"
and "PlutusLedgerApi.V4.Data.Contexts". -}
module Spec.V4.Contexts (tests) where

import Control.Exception
import PlutusLedgerApi.V4 qualified as V4
import PlutusLedgerApi.V4.Contexts qualified as SOP
import PlutusLedgerApi.V4.Data.Contexts qualified as DataV4
import PlutusTx qualified
import PlutusTx.AssocMap qualified as AssocMap
import Test.Tasty
import Test.Tasty.QuickCheck

tests :: TestTree
tests =
  testGroup
    "V4 helper parity (SOP vs Data)"
    [testProperty "helpers agree on random contexts" parityProperty]

parityProperty :: Property
parityProperty = forAll genTestInput $ \input -> ioProperty $ do
  results <- traverse (\h -> (,) (helperName h) <$> helperOutcomes h) (helpers input)
  pure $
    conjoin
      [ counterexample name (dataOutcome === sopOutcome)
      | (name, (sopOutcome, dataOutcome)) <- results
      ]

-- | Outcome of a helper function: either some Data object or error.
type Outcome = Either String V4.Data

outcome :: PlutusTx.ToData a => a -> IO Outcome
outcome = fmap (either (Left . show @ErrorCall) Right) . try . evaluate . PlutusTx.toData

-- | Convert between two types that share the same Data encoding.
viaData :: (PlutusTx.ToData a, PlutusTx.UnsafeFromData b) => a -> b
viaData = PlutusTx.unsafeFromBuiltinData . PlutusTx.toBuiltinData

data TestInput = TestInput
  { ctx :: SOP.ScriptContext
  , tiDatumHash :: V4.DatumHash
  , tiDatum :: V4.Datum
  , tiOutRef :: V4.TxOutRef
  , tiPubKeyHash :: V4.PubKeyHash
  , tiCredential :: V4.Credential
  , tiTxId :: V4.TxId
  , tiIndex :: Integer
  }
  deriving stock (Show)

-- | A V4 helper function
data Helper = Helper
  { helperName :: TestName
  , helperOutcomes :: IO (Outcome, Outcome)
  -- ^ (SOP, Data)
  }

helpers :: TestInput -> [Helper]
helpers TestInput {..} =
  [ check "findOwnInput" (SOP.findOwnInput ctx) (DataV4.findOwnInput ctxD)
  , check
      "findDatum"
      (SOP.findDatum tiDatumHash ti)
      (DataV4.findDatum (viaData tiDatumHash) tiD)
  , check
      "findDatumHash"
      (SOP.findDatumHash tiDatum ti)
      (DataV4.findDatumHash (viaData tiDatum) tiD)
  , check
      "findTxInByTxOutRef"
      (SOP.findTxInByTxOutRef tiOutRef ti)
      (DataV4.findTxInByTxOutRef (viaData tiOutRef) tiD)
  , check
      "findContinuingOutputs"
      (SOP.findContinuingOutputs ctx)
      (DataV4.findContinuingOutputs ctxD)
  , check
      "getContinuingOutputs"
      (SOP.getContinuingOutputs ctx)
      (DataV4.getContinuingOutputs ctxD)
  , check
      "txSignedBy"
      (SOP.txSignedBy ti tiPubKeyHash)
      (DataV4.txSignedBy tiD (viaData tiPubKeyHash))
  , check
      "txGuardedBy"
      (SOP.txGuardedBy ti tiCredential)
      (DataV4.txGuardedBy tiD (viaData tiCredential))
  , check
      "pubKeyOutputsAt"
      (SOP.pubKeyOutputsAt tiPubKeyHash ti)
      (DataV4.pubKeyOutputsAt (viaData tiPubKeyHash) tiD)
  , check
      "valuePaidTo"
      (SOP.valuePaidTo ti tiPubKeyHash)
      (DataV4.valuePaidTo tiD (viaData tiPubKeyHash))
  , check "valueSpent" (SOP.valueSpent ti) (DataV4.valueSpent tiD)
  , check "valueProduced" (SOP.valueProduced ti) (DataV4.valueProduced tiD)
  , check
      "ownCurrencySymbol"
      (SOP.ownCurrencySymbol ctx)
      (DataV4.ownCurrencySymbol ctxD)
  , check
      "spendsOutput"
      (SOP.spendsOutput ti tiTxId tiIndex)
      (DataV4.spendsOutput tiD (viaData tiTxId) tiIndex)
  , check "isTopLevelTx" (SOP.isTopLevelTx ti) (DataV4.isTopLevelTx tiD)
  , check
      "guardingTopTxInfo"
      (SOP.guardingTopTxInfo ctx)
      (DataV4.guardingTopTxInfo ctxD)
  ]
  where
    check :: (PlutusTx.ToData a, PlutusTx.ToData b) => TestName -> a -> b -> Helper
    check name sop dat = Helper name ((,) <$> outcome sop <*> outcome dat)

    ctxD :: DataV4.ScriptContext
    ctxD = viaData ctx

    ti = SOP.scriptContextTxInfo ctx
    tiD = DataV4.scriptContextTxInfo ctxD

genTestInput :: Gen TestInput
genTestInput =
  TestInput
    <$> genContext
    <*> elements datumHashes
    <*> elements datums
    <*> genOutRef
    <*> elements pubKeyHashes
    <*> genCredential
    <*> elements txIds
    <*> choose (0, 3)

genContext :: Gen SOP.ScriptContext
genContext = do
  info <- genTxInfo
  scriptInfo <- genScriptInfo
  pure (V4.ScriptContext info redeemer scriptInfo scriptHash)

genTxInfo :: Gen SOP.TxInfo
genTxInfo = do
  subTxIx <- oneof [pure Nothing, Just <$> choose (0, 3)]
  inputs <- shortListOf genInput
  referenceInputs <- shortListOf genInput
  outputs <- shortListOf genOutput
  guards <- shortListOf genCredential
  datumEntries <- sublistOf datumEntryUni
  pure
    emptyTxInfo
      { SOP.txInfoSubTxIx = subTxIx
      , SOP.txInfoInputs = inputs
      , SOP.txInfoReferenceInputs = referenceInputs
      , SOP.txInfoOutputs = outputs
      , SOP.txInfoGuards = guards
      , SOP.txInfoData = AssocMap.unsafeFromList datumEntries
      }

genScriptInfo :: Gen SOP.ScriptInfo
genScriptInfo =
  oneof
    [ V4.MintingScript <$> elements [currency, otherCurrency]
    , V4.SpendingScript <$> genOutRef <*> oneof [pure Nothing, Just <$> elements datums]
    , V4.WithdrawingScript . V4.AccountId <$> genCredential
    , pure (V4.CertifyingScript 0 certificate)
    , pure (V4.VotingScript voter)
    , pure (V4.ProposingScript 0 proposal)
    , V4.GuardingScript <$> choose (0, 3) <*> pure Nothing
    , V4.GuardingScript <$> choose (0, 3) <*> (Just <$> genTopTxInfo)
    ]

genTopTxInfo :: Gen SOP.TopTxInfo
genTopTxInfo = do
  subTransactions <- shortListOf genTxInfo
  pure
    V4.TopTxInfo
      { V4.topTxInfoSubTransactions = subTransactions
      , V4.topTxInfoDatums = AssocMap.empty
      , V4.topTxInfoStartingAccountBalanceIntervals = V4.AccountBalanceIntervals AssocMap.empty
      , V4.topTxInfoSimplified = mkSimplified subTransactions
      }

genInput :: Gen SOP.TxInInfo
genInput = V4.TxInInfo <$> genOutRef <*> genOutput

genOutput :: Gen V4.TxOut
genOutput = do
  address <- genAddress
  amount <- choose (1, 20)
  withToken <- elements [True, False]
  outputDatum <- elements [V4.NoOutputDatum, V4.OutputDatumHash datumHash, V4.OutputDatum datum]
  referenceScript <- elements [Nothing, Just scriptHash]
  let value
        | withToken = V4.lovelaceValue (V4.Lovelace amount) <> V4.singleton currency token amount
        | otherwise = V4.lovelaceValue (V4.Lovelace amount)
  pure (V4.TxOut address value outputDatum referenceScript)

genAddress :: Gen V4.Address
genAddress = V4.Address <$> genCredential <*> elements [Nothing, Just account, Just otherAccount]

genCredential :: Gen V4.Credential
genCredential =
  oneof
    [ V4.PubKeyCredential <$> elements pubKeyHashes
    , V4.ScriptCredential <$> elements [scriptHash, otherScriptHash]
    ]

genOutRef :: Gen V4.TxOutRef
genOutRef = V4.TxOutRef <$> elements txIds <*> choose (0, 3)

shortListOf :: Gen a -> Gen [a]
shortListOf gen = choose (0, 5) >>= (`vectorOf` gen)

emptyTxInfo :: SOP.TxInfo
emptyTxInfo =
  V4.TxInfo
    { V4.txInfoId = txId
    , V4.txInfoSubTxIx = Nothing
    , V4.txInfoInputs = []
    , V4.txInfoReferenceInputs = []
    , V4.txInfoOutputs = []
    , V4.txInfoMint = V4.emptyMintValue
    , V4.txInfoTxCerts = []
    , V4.txInfoWithdrawals = AssocMap.empty
    , V4.txInfoDirectDeposits = AssocMap.empty
    , V4.txInfoAccountBalanceIntervals = V4.AccountBalanceIntervals AssocMap.empty
    , V4.txInfoValidRange = V4.POSIXTimeRange Nothing Nothing
    , V4.txInfoGuards = []
    , V4.txInfoRequiredTopLevelGuards = AssocMap.empty
    , V4.txInfoRedeemers = AssocMap.empty
    , V4.txInfoData = AssocMap.empty
    , V4.txInfoVotes = AssocMap.empty
    , V4.txInfoProposalProcedures = []
    , V4.txInfoCurrentTreasuryAmount = Nothing
    , V4.txInfoTreasuryDonation = V4.Lovelace 0
    }

mkSimplified :: [SOP.TxInfo] -> SOP.TopTxInfoSimplified
mkSimplified infos =
  V4.TopTxInfoSimplified
    { V4.ttisIds = fmap SOP.txInfoId infos
    , V4.ttisInputs = concatMap SOP.txInfoInputs infos
    , V4.ttisReferenceInputs = concatMap SOP.txInfoReferenceInputs infos
    , V4.ttisOutputs = concatMap SOP.txInfoOutputs infos
    , V4.ttisMints = V4.emptyMintValue
    , V4.ttisBurns = V4.emptyMintValue
    , V4.ttisTxCerts = concatMap SOP.txInfoTxCerts infos
    , V4.ttisWithdrawals = AssocMap.empty
    , V4.ttisDirectDeposits = AssocMap.empty
    , V4.ttisValidRange = V4.POSIXTimeRange Nothing Nothing
    , V4.ttisGuards = concatMap SOP.txInfoGuards infos
    , V4.ttisRequiredTopLevelGuards = []
    , V4.ttisScriptPurposes = []
    , V4.ttisData = AssocMap.empty
    , V4.ttisVotes = AssocMap.empty
    , V4.ttisProposalProcedures = concatMap SOP.txInfoProposalProcedures infos
    , V4.ttisCurrentTreasuryAmount = Nothing
    , V4.ttisTreasuryDonations = V4.Lovelace 0
    }

txId, otherTxId :: V4.TxId
txId = V4.TxId "transaction"
otherTxId = V4.TxId "other transaction"

txIds :: [V4.TxId]
txIds = [txId, otherTxId]

scriptHash, otherScriptHash :: V4.ScriptHash
scriptHash = V4.ScriptHash "script"
otherScriptHash = V4.ScriptHash "other script"

pubKeyHash, otherPubKeyHash :: V4.PubKeyHash
pubKeyHash = V4.PubKeyHash "key"
otherPubKeyHash = V4.PubKeyHash "other key"

pubKeyHashes :: [V4.PubKeyHash]
pubKeyHashes = [pubKeyHash, otherPubKeyHash]

account, otherAccount :: V4.AccountId
account = V4.AccountId (V4.PubKeyCredential otherPubKeyHash)
otherAccount = V4.AccountId (V4.ScriptCredential otherScriptHash)

currency, otherCurrency :: V4.CurrencySymbol
currency = V4.CurrencySymbol "currency"
otherCurrency = V4.CurrencySymbol "other currency"

token :: V4.TokenName
token = V4.TokenName "token"

datumHash, otherDatumHash, duplicateDatumHash, missingDatumHash :: V4.DatumHash
datumHash = V4.DatumHash "datum"
otherDatumHash = V4.DatumHash "other datum"
duplicateDatumHash = V4.DatumHash "duplicate"
missingDatumHash = V4.DatumHash "missing"

datumHashes :: [V4.DatumHash]
datumHashes = [datumHash, otherDatumHash, duplicateDatumHash, missingDatumHash]

datum, otherDatum, missingDatum :: V4.Datum
datum = V4.Datum (PlutusTx.toBuiltinData (42 :: Integer))
otherDatum = V4.Datum (PlutusTx.toBuiltinData (147 :: Integer))
missingDatum = V4.Datum (PlutusTx.toBuiltinData (2026 :: Integer))

datums :: [V4.Datum]
datums = [datum, otherDatum, missingDatum]

datumEntryUni :: [(V4.DatumHash, V4.Datum)]
datumEntryUni = [(datumHash, datum), (otherDatumHash, otherDatum), (duplicateDatumHash, datum)]

redeemer :: V4.Redeemer
redeemer = V4.Redeemer (PlutusTx.toBuiltinData (24 :: Integer))

certificate :: SOP.TxCert
certificate = V4.TxCertUpdateDRep (V4.DRepCredential (V4.PubKeyCredential pubKeyHash))

voter :: SOP.Voter
voter = V4.StakePoolVoter pubKeyHash

proposal :: SOP.ProposalProcedure
proposal = V4.ProposalProcedure (V4.Lovelace 1) (V4.PubKeyCredential pubKeyHash) V4.InfoAction
