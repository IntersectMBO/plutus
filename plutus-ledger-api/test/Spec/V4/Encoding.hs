{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Spec.V4.Encoding (tests) where

import Data.List (nub)
import Data.Map qualified as Map
import PlutusLedgerApi.Data.V4 qualified as DataV4
import PlutusLedgerApi.V3 qualified as V3
import PlutusLedgerApi.V3.Data.MintValue qualified as DataMintValue
import PlutusLedgerApi.V3.MintValue qualified as MintValue
import PlutusLedgerApi.V4 qualified as V4
import PlutusTx qualified
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Blueprint.Definition
import PlutusTx.Blueprint.Schema (Schema (..))
import PlutusTx.Data.AssocMap qualified as DataMap
import PlutusTx.Data.List qualified as DataList
import PlutusTx.Ratio qualified as Ratio
import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, testCase, (@?=))

assertProduct
  :: forall value
   . ( Eq value
     , Show value
     , PlutusTx.ToData value
     , PlutusTx.FromData value
     , PlutusTx.UnsafeFromData value
     )
  => value -> [V4.Data] -> Assertion
assertProduct value fields = do
  PlutusTx.toData value @?= V4.List fields
  PlutusTx.fromData (V4.List fields) @?= Just value
  PlutusTx.unsafeFromBuiltinData (PlutusTx.toBuiltinData value) @?= value
  PlutusTx.fromData @value (V4.Constr 0 fields) @?= Nothing

encodingTest
  :: ( Eq value
     , Show value
     , PlutusTx.ToData value
     , PlutusTx.FromData value
     , PlutusTx.UnsafeFromData value
     , PlutusTx.ToData backed
     )
  => TestName -> value -> backed -> V4.Data -> TestTree
encodingTest name value backed expected = testCase name $ do
  PlutusTx.toData value @?= expected
  PlutusTx.toData backed @?= expected
  PlutusTx.fromData (PlutusTx.toData backed) @?= Just value
  PlutusTx.unsafeFromBuiltinData (PlutusTx.toBuiltinData backed) @?= value

encodingTests
  :: ( Eq value
     , Show value
     , PlutusTx.ToData value
     , PlutusTx.FromData value
     , PlutusTx.UnsafeFromData value
     , PlutusTx.ToData backed
     )
  => TestName -> [(TestName, value, backed, V4.Data)] -> TestTree
encodingTests name =
  testGroup name
    . fmap (\(label, value, backed, expected) -> encodingTest label value backed expected)

tests :: TestTree
tests =
  testGroup
    "V4 list encoding"
    [ testCase "transaction reference" $ do
        assertProduct (V4.TxOutRef txId 2) referenceFields
        PlutusTx.toData (DataV4.TxOutRef dataTxId 2) @?= V4.List referenceFields
        DataV4.txOutRefIdx (DataV4.TxOutRef dataTxId 2) @?= 2
        V4.txOutRefId (V4.TxOutRef txId 2) @?= txId
    , testCase "governance action identifier" $ do
        assertProduct actionId referenceFields
        PlutusTx.toData (DataV4.GovernanceActionId dataTxId 2) @?= V4.List referenceFields
        DataV4.gaidGovActionIx (DataV4.GovernanceActionId dataTxId 2) @?= 2
    , testCase "protocol version" $ do
        assertProduct version [V4.I 11, V4.I 0]
        PlutusTx.toData (DataV4.ProtocolVersion 11 0) @?= PlutusTx.toData version
        DataV4.pvMajor (DataV4.ProtocolVersion 11 0) @?= 11
    , testCase "constitution" $ do
        assertProduct (V4.Constitution Nothing) [nothingData]
        PlutusTx.toData (DataV4.Constitution Nothing) @?= V4.List [nothingData]
    , testCase "rational" $ do
        assertProduct quorum [V4.I 1, V4.I 2]
        PlutusTx.fromData @V4.Rational (V4.List [V4.I 2, V4.I 4]) @?= Just quorum
        PlutusTx.fromData @V4.Rational (V4.List [V4.I 1, V4.I 0]) @?= Nothing
        V4.ratio 1 0 @?= Nothing
    , testCase "committee and nested quorum" $ do
        assertProduct (V4.Committee AssocMap.empty quorum) [V4.Map [], PlutusTx.toData quorum]
        PlutusTx.toData (DataV4.Committee DataMap.empty quorum)
          @?= V4.List [V4.Map [], V4.List [V4.I 1, V4.I 2]]
        DataV4.committeeQuorum (DataV4.Committee DataMap.empty quorum) @?= quorum
    , testCase "proposal and nested governance products" $ do
        let action = V4.HardForkInitiation (Just actionId) version
            dataAction =
              DataV4.HardForkInitiation
                (Just (DataV4.GovernanceActionId dataTxId 2))
                (DataV4.ProtocolVersion 11 0)
            fields = [V4.I 10, PlutusTx.toData credential, PlutusTx.toData action]
        assertProduct (V4.ProposalProcedure (V4.Lovelace 10) credential action) fields
        PlutusTx.toData action
          @?= V4.Constr 1 [V4.Constr 0 [V4.List referenceFields], V4.List [V4.I 11, V4.I 0]]
        PlutusTx.toData (DataV4.ProposalProcedure (DataV4.Lovelace 10) dataCredential dataAction)
          @?= V4.List fields
        PlutusTx.toData
          (DataV4.ppGovernanceAction (DataV4.ProposalProcedure (DataV4.Lovelace 10) dataCredential dataAction))
          @?= PlutusTx.toData action
        PlutusTx.toData (V4.NewConstitution Nothing (V4.Constitution Nothing))
          @?= V4.Constr 5 [nothingData, V4.List [nothingData]]
    , testCase "asset class" $ do
        let asset = V4.assetClass (V4.CurrencySymbol "currency") (V4.TokenName "token")
            dataAsset = DataV4.assetClass (DataV4.CurrencySymbol "currency") (DataV4.TokenName "token")
        assertProduct asset [V4.B "currency", V4.B "token"]
        PlutusTx.toData dataAsset @?= PlutusTx.toData asset
        V4.assetClassValueOf (V4.assetClassValue asset 10) asset @?= 10
        DataV4.assetClassValueOf (DataV4.assetClassValue dataAsset 10) dataAsset @?= 10
    , testCase "nested transaction input and spending purpose" $ do
        let unstakedAddress = V4.Address credential Nothing
            emptyOutput = V4.TxOut unstakedAddress mempty V4.NoOutputDatum Nothing
            dataUnstakedAddress = DataV4.Address dataCredential Nothing
            dataEmptyOutput = DataV4.TxOut dataUnstakedAddress mempty DataV4.NoOutputDatum Nothing
        assertProduct unstakedAddress [PlutusTx.toData credential, nothingData]
        assertProduct emptyOutput [PlutusTx.toData unstakedAddress, V4.Map [], V4.Constr 0 [], nothingData]
        assertProduct
          (V4.TxInInfo reference emptyOutput)
          [V4.List referenceFields, PlutusTx.toData emptyOutput]
        PlutusTx.toData (DataV4.TxInInfo (DataV4.TxOutRef dataTxId 2) dataEmptyOutput)
          @?= PlutusTx.toData (V4.TxInInfo reference emptyOutput)
        PlutusTx.toData (V4.SpendingScript reference Nothing)
          @?= V4.Constr 1 [V4.List referenceFields, nothingData]
    , testCase "time range" $ do
        assertProduct (V4.POSIXTimeRange Nothing Nothing) [nothingData, nothingData]
        PlutusTx.toData (DataV4.POSIXTimeRange Nothing Nothing) @?= V4.List [nothingData, nothingData]
    , testGroup
        "populated products"
        [ encodingTest "address" address dataAddress addressData
        , encodingTest "transaction output" output dataOutput outputData
        , encodingTest "transaction input" (input 2) (dataInput 2) (inputData 2)
        , encodingTest "time range" timeRange dataTimeRange timeRangeData
        , encodingTest "constitution" constitution dataConstitution constitutionData
        , encodingTest
            "committee"
            (V4.Committee committeeMembers quorum)
            (DataV4.Committee dataCommitteeMembers quorum)
            (V4.List [committeeMembersData, V4.List [V4.I 1, V4.I 2]])
        , encodingTest "proposal" proposal dataProposal proposalData
        , encodingTest "transaction info" txInfo dataTxInfo (V4.List txInfoFields)
        , encodingTest "simplified top transaction info" simplified dataSimplified (V4.List simplifiedFields)
        , encodingTest "top transaction info" topInfo dataTopInfo (V4.List topInfoFields)
        , encodingTest "script context" context dataContext (V4.List contextFields)
        , testCase "context products reject legacy constructors" $ do
            assertProduct txInfo txInfoFields
            assertProduct simplified simplifiedFields
            assertProduct topInfo topInfoFields
            assertProduct context contextFields
        ]
    , encodingTests
        "governance actions"
        [
          ( "parameter change"
          , V4.ParameterChange (Just actionId) changedParameters (Just scriptHash)
          , DataV4.ParameterChange (Just dataActionId) dataChangedParameters (Just scriptHash)
          , V4.Constr 0 [justData actionIdData, changedParametersData, justData scriptHashData]
          )
        ,
          ( "hard fork"
          , V4.HardForkInitiation (Just actionId) version
          , DataV4.HardForkInitiation (Just dataActionId) (DataV4.ProtocolVersion 11 0)
          , V4.Constr 1 [justData actionIdData, V4.List [V4.I 11, V4.I 0]]
          )
        ,
          ( "treasury withdrawals"
          , V4.TreasuryWithdrawals (AssocMap.singleton credential (V4.Lovelace 8)) (Just scriptHash)
          , DataV4.TreasuryWithdrawals (DataMap.singleton dataCredential (DataV4.Lovelace 8)) (Just scriptHash)
          , V4.Constr 2 [credentialAmountData 8, justData scriptHashData]
          )
        , ("no confidence", V4.NoConfidence Nothing, DataV4.NoConfidence Nothing, V4.Constr 3 [nothingData])
        , ("update committee", updateCommittee, dataUpdateCommittee, updateCommitteeData)
        ,
          ( "new constitution"
          , V4.NewConstitution (Just actionId) constitution
          , DataV4.NewConstitution (Just dataActionId) dataConstitution
          , V4.Constr 5 [justData actionIdData, constitutionData]
          )
        , ("information", V4.InfoAction, DataV4.InfoAction, V4.Constr 6 [])
        ]
    , encodingTests
        "account balance intervals"
        [
          ( "lower"
          , V4.AccountBalanceLowerBound (V4.Lovelace 10)
          , DataV4.AccountBalanceLowerBound (DataV4.Lovelace 10)
          , V4.Constr 0 [V4.I 10]
          )
        ,
          ( "upper"
          , V4.AccountBalanceUpperBound (V4.Lovelace 20)
          , DataV4.AccountBalanceUpperBound (DataV4.Lovelace 20)
          , V4.Constr 1 [V4.I 20]
          )
        ,
          ( "both"
          , V4.AccountBalanceBothBounds (V4.Lovelace 10) (V4.Lovelace 20)
          , DataV4.AccountBalanceBothBounds (DataV4.Lovelace 10) (DataV4.Lovelace 20)
          , V4.Constr 2 [V4.I 10, V4.I 20]
          )
        ,
          ( "exact"
          , V4.AccountBalanceExact (V4.Lovelace 30)
          , DataV4.AccountBalanceExact (DataV4.Lovelace 30)
          , V4.Constr 3 [V4.I 30]
          )
        ]
    , encodingTests
        "certificates"
        [ ("register account", certificate, dataCertificate, certificateData)
        ,
          ( "unregister account"
          , V4.TxCertUnRegAccount account (V4.Lovelace 8)
          , DataV4.TxCertUnRegAccount dataAccount (DataV4.Lovelace 8)
          , V4.Constr 1 [credentialData, V4.I 8]
          )
        ,
          ( "delegate account"
          , V4.TxCertDelegAccount account delegatee
          , DataV4.TxCertDelegAccount dataAccount dataDelegatee
          , V4.Constr 2 [credentialData, delegateeData]
          )
        ,
          ( "register and delegate account"
          , V4.TxCertRegAccountDeleg account delegatee (V4.Lovelace 9)
          , DataV4.TxCertRegAccountDeleg dataAccount dataDelegatee (DataV4.Lovelace 9)
          , V4.Constr 3 [credentialData, delegateeData, V4.I 9]
          )
        ,
          ( "register DRep"
          , V4.TxCertRegDRep drepCredential (V4.Lovelace 10)
          , DataV4.TxCertRegDRep dataDrepCredential (DataV4.Lovelace 10)
          , V4.Constr 4 [credentialData, V4.I 10]
          )
        ,
          ( "update DRep"
          , V4.TxCertUpdateDRep drepCredential
          , DataV4.TxCertUpdateDRep dataDrepCredential
          , V4.Constr 5 [credentialData]
          )
        ,
          ( "unregister DRep"
          , V4.TxCertUnRegDRep drepCredential (V4.Lovelace 11)
          , DataV4.TxCertUnRegDRep dataDrepCredential (DataV4.Lovelace 11)
          , V4.Constr 6 [credentialData, V4.I 11]
          )
        ,
          ( "register pool"
          , V4.TxCertPoolRegister poolKey (V4.PubKeyHash "vrf")
          , DataV4.TxCertPoolRegister poolKey (DataV4.PubKeyHash "vrf")
          , V4.Constr 7 [V4.B "pool", V4.B "vrf"]
          )
        ,
          ( "retire pool"
          , V4.TxCertPoolRetire poolKey 12
          , DataV4.TxCertPoolRetire poolKey 12
          , V4.Constr 8 [V4.B "pool", V4.I 12]
          )
        ,
          ( "authorize hot committee"
          , V4.TxCertAuthHotCommittee coldCredential hotCredential
          , DataV4.TxCertAuthHotCommittee dataColdCredential dataHotCredential
          , V4.Constr 9 [credentialData, scriptCredentialData]
          )
        ,
          ( "resign cold committee"
          , V4.TxCertResignColdCommittee coldCredential
          , DataV4.TxCertResignColdCommittee dataColdCredential
          , V4.Constr 10 [credentialData]
          )
        ]
    , encodingTests
        "script purposes"
        [
          ( "minting"
          , V4.Minting scriptHash currency
          , DataV4.Minting scriptHash dataCurrency
          , V4.Constr 0 [scriptHashData, V4.B "currency"]
          )
        ,
          ( "spending"
          , V4.Spending scriptHash reference
          , DataV4.Spending scriptHash dataReference
          , V4.Constr 1 [scriptHashData, V4.List referenceFields]
          )
        ,
          ( "withdrawing"
          , V4.Withdrawing scriptHash credential
          , DataV4.Withdrawing scriptHash dataCredential
          , V4.Constr 2 [scriptHashData, credentialData]
          )
        ,
          ( "certifying"
          , V4.Certifying scriptHash 3 certificate
          , DataV4.Certifying scriptHash 3 dataCertificate
          , V4.Constr 3 [scriptHashData, V4.I 3, certificateData]
          )
        ,
          ( "voting"
          , V4.Voting scriptHash voter
          , DataV4.Voting scriptHash dataVoter
          , V4.Constr 4 [scriptHashData, voterData]
          )
        ,
          ( "proposing"
          , V4.Proposing scriptHash 4 proposal
          , DataV4.Proposing scriptHash 4 dataProposal
          , V4.Constr 5 [scriptHashData, V4.I 4, proposalData]
          )
        , ("guarding", purpose, dataPurpose, purposeData)
        ]
    , encodingTests
        "script info"
        [
          ( "minting"
          , V4.MintingScript currency
          , DataV4.MintingScript dataCurrency
          , V4.Constr 0 [V4.B "currency"]
          )
        ,
          ( "spending without datum"
          , V4.SpendingScript reference Nothing
          , DataV4.SpendingScript dataReference Nothing
          , V4.Constr 1 [V4.List referenceFields, nothingData]
          )
        ,
          ( "spending with datum"
          , V4.SpendingScript reference (Just datum)
          , DataV4.SpendingScript dataReference (Just datum)
          , V4.Constr 1 [V4.List referenceFields, justData datumData]
          )
        ,
          ( "withdrawing"
          , V4.WithdrawingScript account
          , DataV4.WithdrawingScript dataAccount
          , V4.Constr 2 [credentialData]
          )
        ,
          ( "certifying"
          , V4.CertifyingScript 3 certificate
          , DataV4.CertifyingScript 3 dataCertificate
          , V4.Constr 3 [V4.I 3, certificateData]
          )
        , ("voting", V4.VotingScript voter, DataV4.VotingScript dataVoter, V4.Constr 4 [voterData])
        ,
          ( "proposing"
          , V4.ProposingScript 4 proposal
          , DataV4.ProposingScript 4 dataProposal
          , V4.Constr 5 [V4.I 4, proposalData]
          )
        ,
          ( "sub-transaction guard"
          , V4.GuardingScript 25 Nothing
          , DataV4.GuardingScript 25 Nothing
          , V4.Constr 6 [V4.I 25, nothingData]
          )
        , ("top-level guard", scriptInfo, dataScriptInfo, scriptInfoData)
        ]
    , encodingTests
        "credentials"
        [ ("public key", credential, dataCredential, credentialData)
        , ("script", scriptCredential, dataScriptCredential, scriptCredentialData)
        ]
    , encodingTests
        "output datum"
        [ ("none", V4.NoOutputDatum, DataV4.NoOutputDatum, V4.Constr 0 [])
        , ("hash", V4.OutputDatumHash datumHash, DataV4.OutputDatumHash datumHash, V4.Constr 1 [V4.B "datum"])
        , ("inline", V4.OutputDatum datum, DataV4.OutputDatum datum, V4.Constr 2 [datumData])
        ]
    , encodingTests
        "DRep"
        [ ("credential", drep, dataDrep, drepData)
        , ("abstain", V4.DRepAlwaysAbstain, DataV4.DRepAlwaysAbstain, V4.Constr 1 [])
        , ("no confidence", V4.DRepAlwaysNoConfidence, DataV4.DRepAlwaysNoConfidence, V4.Constr 2 [])
        ]
    , encodingTests
        "delegatees"
        [ ("stake", V4.DelegStake poolKey, DataV4.DelegStake poolKey, V4.Constr 0 [V4.B "pool"])
        , ("vote", V4.DelegVote drep, DataV4.DelegVote dataDrep, V4.Constr 1 [drepData])
        , ("stake and vote", delegatee, dataDelegatee, delegateeData)
        ]
    , encodingTests
        "voters"
        [ ("committee", voter, dataVoter, voterData)
        ,
          ( "DRep"
          , V4.DRepVoter drepCredential
          , DataV4.DRepVoter dataDrepCredential
          , V4.Constr 1 [credentialData]
          )
        , ("stake pool", V4.StakePoolVoter poolKey, DataV4.StakePoolVoter poolKey, V4.Constr 2 [V4.B "pool"])
        ]
    , encodingTests
        "votes"
        [ ("no", V4.VoteNo, DataV4.VoteNo, V4.Constr 0 [])
        , ("yes", V4.VoteYes, DataV4.VoteYes, V4.Constr 1 [])
        , ("abstain", V4.Abstain, DataV4.Abstain, V4.Constr 2 [])
        ]
    , testGroup
        "transparent wrappers"
        [ encodingTest "account ID" account dataAccount credentialData
        , encodingTest "account balance intervals" (balances 10 20) (dataBalances 10 20) (balancesData 10 20)
        , encodingTest "cold committee credential" coldCredential dataColdCredential credentialData
        , encodingTest "hot committee credential" hotCredential dataHotCredential scriptCredentialData
        , encodingTest "DRep credential" drepCredential dataDrepCredential credentialData
        , encodingTest "changed parameters" changedParameters dataChangedParameters changedParametersData
        , encodingTest "transaction ID" txId dataTxId (V4.B "transaction")
        , encodingTest "time" (V4.POSIXTime 100) (DataV4.POSIXTime 100) (V4.I 100)
        , encodingTest "currency symbol" currency dataCurrency (V4.B "currency")
        , encodingTest "token name" token dataToken (V4.B "token")
        , encodingTest "lovelace" (V4.Lovelace 10) (DataV4.Lovelace 10) (V4.I 10)
        , encodingTest "value" value dataValue (assetMapData 6)
        , encodingTest "mint value" (mintValue 11) (dataMintValue 11) (assetMapData 11)
        ]
    , testCase "legacy encodings unchanged" $ do
        PlutusTx.toData (V3.TxOutRef txId 2) @?= V4.Constr 0 referenceFields
        PlutusTx.toData (V3.GovernanceActionId txId 2) @?= V4.Constr 0 referenceFields
        PlutusTx.toData (V3.ProtocolVersion 11 0) @?= V4.Constr 0 [V4.I 11, V4.I 0]
        PlutusTx.toData (V3.Constitution Nothing) @?= V4.Constr 0 [nothingData]
        PlutusTx.toData (Ratio.unsafeRatio 1 2) @?= V4.Constr 0 [V4.I 1, V4.I 2]
        PlutusTx.toData (V3.assetClass (V3.CurrencySymbol "currency") (V3.TokenName "token"))
          @?= V4.Constr 0 [V4.B "currency", V4.B "token"]
    , testCase "product blueprint definitions" $ do
        let definitions = deriveDefinitions @'[V4.ScriptContext, V4.Committee, V4.AssetClass]
            schemas = definitionsToMap definitions isListSchema
            identifiers = definitionIds definitions
            products =
              [ definitionId @V4.TxOutRef
              , definitionId @V4.GovernanceActionId
              , definitionId @V4.ProtocolVersion
              , definitionId @V4.Constitution
              , definitionId @V4.Committee
              , definitionId @V4.ProposalProcedure
              , definitionId @V4.Rational
              , definitionId @V4.AssetClass
              , definitionId @V4.ScriptContext
              , definitionId @V4.TxInfo
              , definitionId @V4.TopTxInfo
              , definitionId @V4.TopTxInfoSimplified
              , definitionId @V4.Address
              , definitionId @V4.TxOut
              , definitionId @V4.TxInInfo
              , definitionId @V4.POSIXTimeRange
              ]
        assertBool
          "all products use positional list schemas"
          (all (\identifier -> Map.lookup identifier schemas == Just True) products)
        length identifiers @?= length (nub identifiers)
    ]
  where
    txId = V4.TxId "transaction"
    dataTxId = DataV4.TxId "transaction"
    referenceFields = [V4.B "transaction", V4.I 2]
    actionId = V4.GovernanceActionId txId 2
    version = V4.ProtocolVersion 11 0
    quorum = V4.unsafeRatio 1 2
    credential = V4.PubKeyCredential (V4.PubKeyHash "key")
    dataCredential = DataV4.PubKeyCredential (DataV4.PubKeyHash "key")
    nothingData = V4.Constr 1 []
    justData field = V4.Constr 0 [field]
    credentialData = V4.Constr 0 [V4.B "key"]
    scriptHash = V4.ScriptHash "script"
    scriptHashData = V4.B "script"
    scriptCredential = V4.ScriptCredential scriptHash
    dataScriptCredential = DataV4.ScriptCredential scriptHash
    scriptCredentialData = V4.Constr 1 [scriptHashData]
    account = V4.AccountId credential
    dataAccount = DataV4.AccountId dataCredential
    coldCredential = V4.ColdCommitteeCredential credential
    dataColdCredential = DataV4.ColdCommitteeCredential dataCredential
    hotCredential = V4.HotCommitteeCredential scriptCredential
    dataHotCredential = DataV4.HotCommitteeCredential dataScriptCredential
    drepCredential = V4.DRepCredential credential
    dataDrepCredential = DataV4.DRepCredential dataCredential
    drep = V4.DRep drepCredential
    dataDrep = DataV4.DRep dataDrepCredential
    drepData = V4.Constr 0 [credentialData]
    poolKey = V4.PubKeyHash "pool"
    delegatee = V4.DelegStakeVote poolKey drep
    dataDelegatee = DataV4.DelegStakeVote poolKey dataDrep
    delegateeData = V4.Constr 2 [V4.B "pool", drepData]
    voter = V4.CommitteeVoter hotCredential
    dataVoter = DataV4.CommitteeVoter dataHotCredential
    voterData = V4.Constr 0 [scriptCredentialData]
    dataActionId = DataV4.GovernanceActionId dataTxId 2
    actionIdData = V4.List referenceFields
    committeeMembers = AssocMap.singleton coldCredential 2
    dataCommitteeMembers = DataMap.singleton dataColdCredential (2 :: Integer)
    committeeMembersData = V4.Map [(credentialData, V4.I 2)]
    constitution = V4.Constitution (Just scriptHash)
    dataConstitution = DataV4.Constitution (Just scriptHash)
    constitutionData = V4.List [justData scriptHashData]
    changedParametersData = V4.Map [(V4.I 0, V4.I 42)]
    changedParameters = V4.ChangedParameters (PlutusTx.dataToBuiltinData changedParametersData)
    dataChangedParameters = DataV4.ChangedParameters (PlutusTx.dataToBuiltinData changedParametersData)
    updateCommittee = V4.UpdateCommittee (Just actionId) [coldCredential] committeeMembers quorum
    dataUpdateCommittee =
      DataV4.UpdateCommittee
        (Just dataActionId)
        (DataList.fromSOP [dataColdCredential])
        dataCommitteeMembers
        quorum
    updateCommitteeData =
      V4.Constr
        4
        [justData actionIdData, V4.List [credentialData], committeeMembersData, V4.List [V4.I 1, V4.I 2]]
    proposal = V4.ProposalProcedure (V4.Lovelace 17) credential updateCommittee
    dataProposal = DataV4.ProposalProcedure (DataV4.Lovelace 17) dataCredential dataUpdateCommittee
    proposalData = V4.List [V4.I 17, credentialData, updateCommitteeData]
    reference = V4.TxOutRef txId 2
    dataReference = DataV4.TxOutRef dataTxId 2
    currency = V4.CurrencySymbol "currency"
    dataCurrency = DataV4.CurrencySymbol "currency"
    token = V4.TokenName "token"
    dataToken = DataV4.TokenName "token"
    value = V4.singleton currency token 6
    dataValue = DataV4.singleton dataCurrency dataToken 6
    assetMapData amount = V4.Map [(V4.B "currency", V4.Map [(V4.B "token", V4.I amount)])]
    mintValue amount = MintValue.UnsafeMintValue (AssocMap.singleton currency (AssocMap.singleton token amount))
    dataMintValue amount =
      DataMintValue.UnsafeMintValue (DataMap.singleton dataCurrency (DataMap.singleton dataToken amount))
    datumHash = V4.DatumHash "datum"
    datumData = V4.I 15
    datum = V4.Datum (PlutusTx.dataToBuiltinData datumData)
    address = V4.Address credential (Just account)
    dataAddress = DataV4.Address dataCredential (Just dataAccount)
    addressData = V4.List [credentialData, justData credentialData]
    output = V4.TxOut address value (V4.OutputDatum datum) (Just scriptHash)
    dataOutput = DataV4.TxOut dataAddress dataValue (DataV4.OutputDatum datum) (Just scriptHash)
    outputData = V4.List [addressData, assetMapData 6, V4.Constr 2 [datumData], justData scriptHashData]
    input index = V4.TxInInfo (V4.TxOutRef txId index) output
    dataInput index = DataV4.TxInInfo (DataV4.TxOutRef dataTxId index) dataOutput
    inputData index = V4.List [V4.List [V4.B "transaction", V4.I index], outputData]
    timeRange = V4.POSIXTimeRange (Just (V4.POSIXTime 100)) (Just (V4.POSIXTime 200))
    dataTimeRange = DataV4.POSIXTimeRange (Just (DataV4.POSIXTime 100)) (Just (DataV4.POSIXTime 200))
    timeRangeData = V4.List [justData (V4.I 100), justData (V4.I 200)]
    certificate = V4.TxCertRegAccount account (V4.Lovelace 7)
    dataCertificate = DataV4.TxCertRegAccount dataAccount (DataV4.Lovelace 7)
    certificateData = V4.Constr 0 [credentialData, V4.I 7]
    balances lower upper =
      V4.AccountBalanceIntervals
        (AssocMap.singleton account (V4.AccountBalanceBothBounds (V4.Lovelace lower) (V4.Lovelace upper)))
    dataBalances lower upper =
      DataV4.AccountBalanceIntervals
        ( DataMap.singleton
            dataAccount
            (DataV4.AccountBalanceBothBounds (DataV4.Lovelace lower) (DataV4.Lovelace upper))
        )
    balancesData lower upper = V4.Map [(credentialData, V4.Constr 2 [V4.I lower, V4.I upper])]
    credentialAmountData amount = V4.Map [(credentialData, V4.I amount)]
    purpose = V4.Guarding scriptHash 14
    dataPurpose = DataV4.Guarding scriptHash 14
    purposeData = V4.Constr 6 [scriptHashData, V4.I 14]
    redeemer = V4.Redeemer (PlutusTx.toBuiltinData (24 :: Integer))
    votes = AssocMap.singleton voter (AssocMap.singleton actionId V4.VoteYes)
    dataVotes = DataMap.singleton dataVoter (DataMap.singleton dataActionId DataV4.VoteYes)
    votesData = V4.Map [(voterData, V4.Map [(actionIdData, V4.Constr 1 [])])]
    txInfo =
      V4.TxInfo
        { V4.txInfoId = txId
        , V4.txInfoSubTxIx = Just 3
        , V4.txInfoInputs = [input 2]
        , V4.txInfoReferenceInputs = [input 3]
        , V4.txInfoOutputs = [output]
        , V4.txInfoMint = mintValue 11
        , V4.txInfoTxCerts = [certificate]
        , V4.txInfoWithdrawals = AssocMap.singleton credential (V4.Lovelace 8)
        , V4.txInfoDirectDeposits = AssocMap.singleton credential (V4.Lovelace 9)
        , V4.txInfoAccountBalanceIntervals = balances 10 20
        , V4.txInfoValidRange = timeRange
        , V4.txInfoGuards = [credential]
        , V4.txInfoRequiredTopLevelGuards = AssocMap.singleton scriptCredential (Just datum)
        , V4.txInfoRedeemers = AssocMap.singleton purpose redeemer
        , V4.txInfoData = AssocMap.singleton datumHash datum
        , V4.txInfoVotes = votes
        , V4.txInfoProposalProcedures = [proposal]
        , V4.txInfoCurrentTreasuryAmount = Just (V4.Lovelace 18)
        , V4.txInfoTreasuryDonation = V4.Lovelace 19
        }
    dataTxInfo =
      DataV4.TxInfo
        { DataV4.txInfoId = dataTxId
        , DataV4.txInfoSubTxIx = Just 3
        , DataV4.txInfoInputs = DataList.fromSOP [dataInput 2]
        , DataV4.txInfoReferenceInputs = DataList.fromSOP [dataInput 3]
        , DataV4.txInfoOutputs = DataList.fromSOP [dataOutput]
        , DataV4.txInfoMint = dataMintValue 11
        , DataV4.txInfoTxCerts = DataList.fromSOP [dataCertificate]
        , DataV4.txInfoWithdrawals = DataMap.singleton dataCredential (DataV4.Lovelace 8)
        , DataV4.txInfoDirectDeposits = DataMap.singleton dataCredential (DataV4.Lovelace 9)
        , DataV4.txInfoAccountBalanceIntervals = dataBalances 10 20
        , DataV4.txInfoValidRange = dataTimeRange
        , DataV4.txInfoGuards = DataList.fromSOP [dataCredential]
        , DataV4.txInfoRequiredTopLevelGuards = DataMap.singleton dataScriptCredential (Just datum)
        , DataV4.txInfoRedeemers = DataMap.singleton dataPurpose redeemer
        , DataV4.txInfoData = DataMap.singleton datumHash datum
        , DataV4.txInfoVotes = dataVotes
        , DataV4.txInfoProposalProcedures = DataList.fromSOP [dataProposal]
        , DataV4.txInfoCurrentTreasuryAmount = Just (DataV4.Lovelace 18)
        , DataV4.txInfoTreasuryDonation = DataV4.Lovelace 19
        }
    txInfoFields =
      [ V4.B "transaction"
      , justData (V4.I 3)
      , V4.List [inputData 2]
      , V4.List [inputData 3]
      , V4.List [outputData]
      , assetMapData 11
      , V4.List [certificateData]
      , credentialAmountData 8
      , credentialAmountData 9
      , balancesData 10 20
      , timeRangeData
      , V4.List [credentialData]
      , V4.Map [(scriptCredentialData, justData datumData)]
      , V4.Map [(purposeData, V4.I 24)]
      , V4.Map [(V4.B "datum", datumData)]
      , votesData
      , V4.List [proposalData]
      , justData (V4.I 18)
      , V4.I 19
      ]
    simplified =
      V4.TopTxInfoSimplified
        { V4.ttisIds = [txId]
        , V4.ttisInputs = [input 2]
        , V4.ttisReferenceInputs = [input 3]
        , V4.ttisOutputs = [output]
        , V4.ttisMints = mintValue 12
        , V4.ttisBurns = mintValue (-13)
        , V4.ttisTxCerts = [certificate]
        , V4.ttisWithdrawals = AssocMap.singleton credential (V4.Lovelace 8)
        , V4.ttisDirectDeposits = AssocMap.singleton credential (V4.Lovelace 9)
        , V4.ttisValidRange = timeRange
        , V4.ttisGuards = [credential]
        , V4.ttisRequiredTopLevelGuards = [scriptCredential]
        , V4.ttisScriptPurposes = [purpose]
        , V4.ttisData = AssocMap.singleton datumHash datum
        , V4.ttisVotes = votes
        , V4.ttisProposalProcedures = [proposal]
        , V4.ttisCurrentTreasuryAmount = Just (V4.Lovelace 18)
        , V4.ttisTreasuryDonations = V4.Lovelace 19
        }
    dataSimplified =
      DataV4.TopTxInfoSimplified
        { DataV4.ttisIds = DataList.fromSOP [dataTxId]
        , DataV4.ttisInputs = DataList.fromSOP [dataInput 2]
        , DataV4.ttisReferenceInputs = DataList.fromSOP [dataInput 3]
        , DataV4.ttisOutputs = DataList.fromSOP [dataOutput]
        , DataV4.ttisMints = dataMintValue 12
        , DataV4.ttisBurns = dataMintValue (-13)
        , DataV4.ttisTxCerts = DataList.fromSOP [dataCertificate]
        , DataV4.ttisWithdrawals = DataMap.singleton dataCredential (DataV4.Lovelace 8)
        , DataV4.ttisDirectDeposits = DataMap.singleton dataCredential (DataV4.Lovelace 9)
        , DataV4.ttisValidRange = dataTimeRange
        , DataV4.ttisGuards = DataList.fromSOP [dataCredential]
        , DataV4.ttisRequiredTopLevelGuards = DataList.fromSOP [dataScriptCredential]
        , DataV4.ttisScriptPurposes = DataList.fromSOP [dataPurpose]
        , DataV4.ttisData = DataMap.singleton datumHash datum
        , DataV4.ttisVotes = dataVotes
        , DataV4.ttisProposalProcedures = DataList.fromSOP [dataProposal]
        , DataV4.ttisCurrentTreasuryAmount = Just (DataV4.Lovelace 18)
        , DataV4.ttisTreasuryDonations = DataV4.Lovelace 19
        }
    simplifiedFields =
      [ V4.List [V4.B "transaction"]
      , V4.List [inputData 2]
      , V4.List [inputData 3]
      , V4.List [outputData]
      , assetMapData 12
      , assetMapData (-13)
      , V4.List [certificateData]
      , credentialAmountData 8
      , credentialAmountData 9
      , timeRangeData
      , V4.List [credentialData]
      , V4.List [scriptCredentialData]
      , V4.List [purposeData]
      , V4.Map [(V4.B "datum", datumData)]
      , votesData
      , V4.List [proposalData]
      , justData (V4.I 18)
      , V4.I 19
      ]
    topInfo = V4.TopTxInfo [txInfo] (AssocMap.singleton txId datum) (balances 31 32) simplified
    dataTopInfo =
      DataV4.TopTxInfo
        (DataList.fromSOP [dataTxInfo])
        (DataMap.singleton dataTxId datum)
        (dataBalances 31 32)
        dataSimplified
    topInfoFields =
      [ V4.List [V4.List txInfoFields]
      , V4.Map [(V4.B "transaction", datumData)]
      , balancesData 31 32
      , V4.List simplifiedFields
      ]
    scriptInfo = V4.GuardingScript 25 (Just topInfo)
    dataScriptInfo = DataV4.GuardingScript 25 (Just dataTopInfo)
    scriptInfoData = V4.Constr 6 [V4.I 25, justData (V4.List topInfoFields)]
    context = V4.ScriptContext txInfo redeemer scriptInfo scriptHash
    dataContext = DataV4.ScriptContext dataTxInfo redeemer dataScriptInfo scriptHash
    contextFields = [V4.List txInfoFields, V4.I 24, scriptInfoData, scriptHashData]

isListSchema :: Schema referencedTypes -> Bool
isListSchema SchemaListTuple {} = True
isListSchema _ = False

definitionIds :: Definitions referencedTypes -> [DefinitionId]
definitionIds NoDefinitions = []
definitionIds (AddDefinition (MkDefinition identifier _) rest) = identifier : definitionIds rest
