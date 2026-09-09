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
import PlutusLedgerApi.V4 qualified as V4
import PlutusTx qualified
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.Blueprint.Definition
import PlutusTx.Blueprint.Schema (Schema (..))
import PlutusTx.Data.AssocMap qualified as DataMap
import PlutusTx.Ratio qualified as Ratio
import Test.Tasty (TestTree, testGroup)
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
        let address = V4.Address credential Nothing
            output = V4.TxOut address mempty V4.NoOutputDatum Nothing
            reference = V4.TxOutRef txId 2
            dataAddress = DataV4.Address dataCredential Nothing
            dataOutput = DataV4.TxOut dataAddress mempty DataV4.NoOutputDatum Nothing
        assertProduct address [PlutusTx.toData credential, nothingData]
        assertProduct output [PlutusTx.toData address, V4.Map [], V4.Constr 0 [], nothingData]
        assertProduct (V4.TxInInfo reference output) [V4.List referenceFields, PlutusTx.toData output]
        PlutusTx.toData (DataV4.TxInInfo (DataV4.TxOutRef dataTxId 2) dataOutput)
          @?= PlutusTx.toData (V4.TxInInfo reference output)
        PlutusTx.toData (V4.SpendingScript reference Nothing)
          @?= V4.Constr 1 [V4.List referenceFields, nothingData]
    , testCase "time range" $ do
        assertProduct (V4.POSIXTimeRange Nothing Nothing) [nothingData, nothingData]
        PlutusTx.toData (DataV4.POSIXTimeRange Nothing Nothing) @?= V4.List [nothingData, nothingData]
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

isListSchema :: Schema referencedTypes -> Bool
isListSchema SchemaListTuple {} = True
isListSchema _ = False

definitionIds :: Definitions referencedTypes -> [DefinitionId]
definitionIds NoDefinitions = []
definitionIds (AddDefinition (MkDefinition identifier _) rest) = identifier : definitionIds rest
