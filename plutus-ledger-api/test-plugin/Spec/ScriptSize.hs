{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module Spec.ScriptSize where

import PlutusTx.Prelude
import Prelude qualified as Haskell

import Control.Lens ((&), (^.))
import Data.ByteString.Short qualified as SBS
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekParametersForTesting)
import PlutusCore.StdLib.Data.Unit (unitval)
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3 qualified as V3
import PlutusLedgerApi.V3.MintValue (emptyMintValue)
import PlutusTx (CompiledCode, liftCodeDef, unsafeApplyCode)
import PlutusTx.AssocMap qualified as Map
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Code (getPlc)
import PlutusTx.TH (compile)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (Assertion, assertBool, assertEqual, assertFailure, testCase)
import UntypedPlutusCore.Core.Type (progTerm)
import UntypedPlutusCore.Evaluation.Machine.Cek (_cekReportResult, cekResultToEither, counting,
                                                 noEmitter)
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal (NTerm, runCekDeBruijn)

tests :: TestTree
tests =
  testGroup
    "Script Size"
    [ testCase "V2 Script Size" do
        let sizeV2 = SBS.length (V2.serialiseCompiledCode codeV2)
        assertBool "Size V2 script" $ sizeV2 Haskell.< 100
    , testCase "V3 Script Size" do
        let sizeV3 = SBS.length (V3.serialiseCompiledCode codeV3)
        assertBool "Size V3 script" $ sizeV3 Haskell.> 1700
    , testCase "V3 Script Size (lazy decoding)" do
        let sizeV3s = SBS.length (V3.serialiseCompiledCode codeV3lazy)
        assertBool "Size V3 script with a lazy decoding" $ sizeV3s Haskell.< 100
    , testCase "V3 script evaluates correctly" do
        unsafeApplyCode codeV3 (liftCodeDef (V3.toBuiltinData dummyScriptContext))
          & assertResult unitval
    , testCase "V3 (lazy) script evaluates correctly" do
        unsafeApplyCode codeV3lazy (liftCodeDef (V3.toBuiltinData dummyScriptContext))
          & assertResult unitval
    ]

codeV2 :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
codeV2 = $$(compile [||validatorV2||])
  where
    validatorV2 :: BuiltinData -> BuiltinData -> BuiltinData -> ()
    validatorV2 datumBuiltinData redeemerBuiltinData _scriptContext =
      if expected == redeemer && expected == datum
        then ()
        else error ()
      where
        redeemer :: Integer
        redeemer = V2.unsafeFromBuiltinData redeemerBuiltinData

        datum :: Integer
        datum = V2.unsafeFromBuiltinData datumBuiltinData

codeV3 :: CompiledCode (BuiltinData -> BuiltinUnit)
codeV3 = $$(compile [||validatorV3||])
  where
    validatorV3 :: BuiltinData -> BuiltinUnit
    validatorV3 scriptContext =
      if expected == redeemer && Haskell.Just expected == datum
        then BI.unitval
        else error ()
      where
        redeemer :: Integer
        redeemer = V3.unsafeFromBuiltinData redeemerBuiltinData

        datum :: Haskell.Maybe Integer
        datum = V3.unsafeFromBuiltinData . V3.getDatum <$> optionalDatum

        (redeemerBuiltinData, optionalDatum) =
          case V3.unsafeFromBuiltinData scriptContext of
            V3.ScriptContext
              _txInfo
              (V3.Redeemer redeemerBuiltinData')
              (V3.SpendingScript _txOutRef optionalDatum') ->
                (redeemerBuiltinData', optionalDatum')
            _ -> error ()

codeV3lazy :: CompiledCode (BuiltinData -> BuiltinUnit)
codeV3lazy = $$(compile [||validatorV3smart||])
  where
    validatorV3smart :: BuiltinData -> BuiltinUnit
    validatorV3smart scriptContext =
      if expected == redeemer && expected == datum
        then BI.unitval
        else error ()
      where
        redeemerFollowedByScriptInfo :: BI.BuiltinList BuiltinData
        redeemerFollowedByScriptInfo = BI.tail (constrArgs scriptContext)

        redeemerBuiltinData :: BuiltinData
        redeemerBuiltinData = BI.head redeemerFollowedByScriptInfo

        scriptInfoData :: BuiltinData
        scriptInfoData = BI.head (BI.tail redeemerFollowedByScriptInfo)

        datumData :: BuiltinData
        datumData = BI.head (constrArgs (BI.head (BI.tail (constrArgs scriptInfoData))))

        redeemer :: Integer
        redeemer = V3.unsafeFromBuiltinData redeemerBuiltinData

        datum :: Integer
        datum = V3.unsafeFromBuiltinData (V3.getDatum (V3.unsafeFromBuiltinData datumData))

constrArgs :: BuiltinData -> BI.BuiltinList BuiltinData
constrArgs = BI.snd . BI.unsafeDataAsConstr

expected :: Integer
expected = 42

{-
  Constr
    0
    [ Constr
      0
      [ List []
      , List []
      , List []
      , I 1000000
      , Map []
      , List []
      , Map []
      , Constr 0
        [ Constr 0 [Constr 0 []
        , Constr 1 []]
        , Constr 0 [Constr 2 []
        , Constr 1 []]
        ]
      , List []
      , Map []
      , Map []
      , B ""
      , Map []
      , List []
      , Constr 1 []
      , Constr 1 []
      ]
    , I 42
    , Constr
        1
        [ Constr 0 [B "", I 100]
        , Constr 0 [I 42]
        ]
    ]
-}
dummyScriptContext :: V3.ScriptContext
dummyScriptContext =
  V3.ScriptContext
    { V3.scriptContextTxInfo =
        V3.TxInfo
          { V3.txInfoInputs = []
          , V3.txInfoReferenceInputs = []
          , V3.txInfoOutputs = []
          , V3.txInfoFee = 1000000 :: V3.Lovelace
          , V3.txInfoMint = emptyMintValue
          , V3.txInfoTxCerts = []
          , V3.txInfoWdrl = Map.empty
          , V3.txInfoValidRange =
              V3.Interval
                { V3.ivFrom = V3.LowerBound V3.NegInf True
                , V3.ivTo = V3.UpperBound V3.PosInf True
                }
          , V3.txInfoSignatories = []
          , V3.txInfoRedeemers = Map.empty
          , V3.txInfoData = Map.empty
          , V3.txInfoId = V3.TxId mempty
          , V3.txInfoVotes = Map.empty
          , V3.txInfoProposalProcedures = []
          , V3.txInfoCurrentTreasuryAmount = Haskell.Nothing
          , V3.txInfoTreasuryDonation = Haskell.Nothing
          }
    , V3.scriptContextRedeemer =
        V3.Redeemer (V3.toBuiltinData expected)
    , V3.scriptContextScriptInfo =
        V3.SpendingScript
          V3.TxOutRef
            { V3.txOutRefId = V3.TxId mempty
            , V3.txOutRefIdx = 100 :: Integer
            }
          (Haskell.Just (V3.Datum (V3.toBuiltinData expected)))
    }

assertResult :: NTerm DefaultUni DefaultFun () -> CompiledCode a -> Assertion
assertResult expectedResult code = do
  let plc = getPlc code ^. progTerm
      tidy = cekResultToEither . _cekReportResult
  case tidy $ runCekDeBruijn defaultCekParametersForTesting counting noEmitter plc of
    Left ex ->
      assertFailure $ Haskell.show ex
    Right actualResult ->
      assertEqual "Evaluation has succeeded" expectedResult actualResult
