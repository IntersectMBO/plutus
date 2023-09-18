-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Spec.Versions (tests) where

import PlutusCore as PLC
import PlutusCore.Data as PLC
import PlutusCore.MkPlc as PLC
import PlutusCore.Version as PLC
import PlutusLedgerApi.Common
import PlutusLedgerApi.Common.Versions
import PlutusPrelude
import UntypedPlutusCore as UPLC

import PlutusLedgerApi.Test.Scripts
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3 qualified as V3

import Data.ByteString qualified as BS
import Data.ByteString.Short qualified as BSS
import Data.Either
import Data.Foldable (for_)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

tests :: TestTree
tests = testGroup "versions"
    [ testLedgerLanguages
    , testBuiltinVersions
    , testLanguageVersions
    , testRmdr
    ]

testLedgerLanguages :: TestTree
testLedgerLanguages = testGroup "ledger languages"
    [ testProperty "v1 not before but after" $ prop_notBeforeButAfter V1.deserialiseScript alonzoPV
    , testProperty "v2 not before but after" $ prop_notBeforeButAfter V2.deserialiseScript vasilPV
    , testProperty "v3 not before but after" $ prop_notBeforeButAfter V3.deserialiseScript conwayPV
    , testProperty "protocol-versions can add but not remove ledger languages" $
        \pvA pvB -> pvA < pvB ==> ledgerLanguagesAvailableIn pvA `Set.isSubsetOf` ledgerLanguagesAvailableIn pvB
    ]
  where
    prop_notBeforeButAfter :: (MajorProtocolVersion -> SerialisedScript -> Either ScriptDecodeError b)
                           -> MajorProtocolVersion -> MajorProtocolVersion -> Bool
    prop_notBeforeButAfter phase1Func expectedPv genPv =
        -- run phase 1 on an example script
        let resPhase1 = phase1Func genPv errorScript
        in if genPv < expectedPv
           -- generated an old protocol version
           then
               case resPhase1 of
                   Left LedgerLanguageNotAvailableError{} -> True
                   _                                      -> False
           -- generated an eq or gt the expected protocol version
           else isRight resPhase1

deriving newtype instance Arbitrary MajorProtocolVersion

testBuiltinVersions :: TestTree
testBuiltinVersions = testGroup "builtins"
    [ testCase "all builtins are available some time" $
            let allPvBuiltins = fold $ Map.elems builtinsIntroducedIn
                allBuiltins = enumerate @DefaultFun
            in for_ allBuiltins $ \f -> assertBool (show f) (f `Set.member` allPvBuiltins)
    , testCase "builtins aren't available before Alonzo" $
        assertBool "empty" (Set.null $ builtinsAvailableIn PlutusV1 maryPV)
    , testCase "serializeData is only available in l2,Vasil and after" $ do
         assertBool "in l1,Alonzo" $ isLeft $ V1.deserialiseScript alonzoPV serialiseDataExScript
         assertBool "in l1,Vasil" $ isLeft $ V1.deserialiseScript vasilPV serialiseDataExScript
         assertBool "in l2,Alonzo" $ isLeft $ V2.deserialiseScript alonzoPV serialiseDataExScript
         assertBool "in l3,Alonzo" $ isLeft $ V3.deserialiseScript alonzoPV serialiseDataExScript
         assertBool "not in l2,Vasil" $ isRight $ V2.deserialiseScript vasilPV serialiseDataExScript
         assertBool "not in l3,future" $ isRight $ V3.deserialiseScript futurePV serialiseDataExScript
    , testCase "bls,keccak256,blake2b224 only available in l3,Future and after" $
         for_ [blsExScript, keccak256ExScript, blake2b224ExScript] $ \script -> do
             assertBool "in l1,Alonzo" $ isLeft $ V1.deserialiseScript alonzoPV script
             assertBool "in l1,Vasil" $ isLeft $ V1.deserialiseScript vasilPV script
             assertBool "in l2,Alonzo" $ isLeft $ V2.deserialiseScript alonzoPV script
             assertBool "in l3,Alonzo" $ isLeft $ V3.deserialiseScript alonzoPV script
             assertBool "in l2,Valentine" $ isLeft $ V2.deserialiseScript valentinePV script
             assertBool "not in l3,future" $ isRight $ V3.deserialiseScript futurePV script
    ]

testRmdr :: TestTree
testRmdr = testGroup "rmdr"
    [ testCase "remdr" $ do
         assertBool "remdr1" $ isRight $ V1.deserialiseScript valentinePV $ errorScript <> "remdr1"
         assertBool "remdr2" $ isRight $ V2.deserialiseScript valentinePV $ errorScript <> "remdr2"
         assertBool "remdr1c" $ isRight $ V1.deserialiseScript conwayPV $ errorScript <> "remdr1"
         assertBool "remdr2c" $ isRight $ V2.deserialiseScript conwayPV $ errorScript <> "remdr2"
         assertEqual "remdr3" (RemainderError "remdr3") $ fromLeft (Prelude.error "Expected Reft, got Right") $ V3.deserialiseScript conwayPV $ errorScript <> "remdr3"
    , testProperty "remdr1gen"$ \remdr -> isRight $ V1.deserialiseScript valentinePV $ errorScript <> BSS.pack remdr
    , testProperty "remdr2gen"$ \remdr -> isRight $ V2.deserialiseScript valentinePV $ errorScript <> BSS.pack remdr
    , testProperty "remdr1genc"$ \remdr -> isRight $ V1.deserialiseScript conwayPV $ errorScript <> BSS.pack remdr
    , testProperty "remdr2genc"$ \remdr -> isRight $ V2.deserialiseScript conwayPV $ errorScript <> BSS.pack remdr
    -- we cannot make the same property as above for remdr3gen because it may generate valid bytestring append extensions to the original script
    -- a more sophisticated one could work though
    ]

-- See Note [Checking the Plutus Core language version] for why these have to use mkTermToEvaluate
testLanguageVersions :: TestTree
testLanguageVersions = testGroup "Plutus Core language versions"
  [ testCase "v1.1.0 is available in l3,future and not before" $ do
      -- `LedgerLanguageNotAvailableError` is checked in `deserialiseScript`
      assertBool "in l3,Vasil" $ isLeft $ uplcToScriptForEvaluation PlutusV3 vasilPV v110script
      -- `PlutusCoreLanguageNotAvailableError` is checked in `mkTermToEvaluate`
      assertBool "in l2,future" $ isLeft $ mkTermToEvaluate PlutusV2 conwayPV (either (Prelude.error . show) id (V2.deserialiseScript conwayPV $ serialiseUPLC v110script)) []
      -- Both `deserialiseScript` and `mkTermToEvaluate` should succeed
      assertBool "not in l3,future" $ isRight $ mkTermToEvaluate PlutusV3 conwayPV (either (Prelude.error . show) id (V3.deserialiseScript conwayPV $ serialiseUPLC v110script)) []
    -- The availability of `case` and `constr` is checked in `deserialise`
  , testCase "constr is not available with v1.0.0 ever" $ assertBool "in l3,future" $ isLeft $ uplcToScriptForEvaluation PlutusV3 conwayPV badConstrScript
  , testCase "case is not available with v1.0.0 ever" $ assertBool "in l3,future" $ isLeft $ uplcToScriptForEvaluation PlutusV3 conwayPV badCaseScript
  ]

-- * UPLC written examples to test

serialiseDataExScript :: SerialisedScript
serialiseDataExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
    UPLC.Apply () (UPLC.Builtin () PLC.SerialiseData) (PLC.mkConstant () $ I 1)

errorScript :: SerialisedScript
errorScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $ UPLC.Error ()

v110script :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
v110script = UPLC.Program () PLC.plcVersion110 $ UPLC.Constr () 0 []

badConstrScript :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
badConstrScript = UPLC.Program () PLC.plcVersion100 $ UPLC.Constr () 0 []

badCaseScript :: UPLC.Program UPLC.DeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
badCaseScript = UPLC.Program () PLC.plcVersion100 $ UPLC.Case () (UPLC.Error ()) []

-- Note that bls can work also with plcversion==1.0.0
blsExScript :: SerialisedScript
blsExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
     builtin () Bls12_381_G1_uncompress @@ [mkConstant () $ BS.pack (0xc0 : replicate 47 0x00)]

-- Note that keccak can work also with plcversion==1.0.0
keccak256ExScript :: SerialisedScript
keccak256ExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
    builtin () Keccak_256 @@ [mkConstant @BS.ByteString () "hashme"]

-- Note that blake2b224 can work also with plcversion==1.0.0
blake2b224ExScript :: SerialisedScript
blake2b224ExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
    builtin () Blake2b_224 @@ [mkConstant @BS.ByteString () "hashme"]
