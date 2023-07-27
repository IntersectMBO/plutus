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
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3 qualified as V3
import PlutusPrelude
import UntypedPlutusCore as UPLC

import Control.Monad.Except
import Data.ByteString qualified as BS
import Data.ByteString.Short qualified as BSS
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
    [ testProperty "v1 not before but after" $ prop_notBeforeButAfter V1.assertScriptWellFormed alonzoPV
    , testProperty "v2 not before but after" $ prop_notBeforeButAfter V2.assertScriptWellFormed vasilPV
    , testProperty "v3 not before but after" $ prop_notBeforeButAfter V3.assertScriptWellFormed conwayPV
    , testProperty "protocol-versions can add but not remove ledger languages" $
        \pvA pvB -> pvA < pvB ==> ledgerLanguagesAvailableIn pvA `Set.isSubsetOf` ledgerLanguagesAvailableIn pvB
    ]
  where
    prop_notBeforeButAfter :: (ProtocolVersion -> SerialisedScript -> Except ScriptDecodeError b)
                           -> ProtocolVersion -> ProtocolVersion -> Bool
    prop_notBeforeButAfter phase1Func expectedPv genPv =
        -- run phase 1 on an example script
        let resPhase1 = runExcept $ phase1Func genPv errorScript
        in if genPv < expectedPv
           -- generated an old protocol version
           then
               case resPhase1 of
                   Left LedgerLanguageNotAvailableError{} -> True
                   _                                      -> False
           -- generated an eq or gt the expected protocol version
           else isRight resPhase1


instance Arbitrary ProtocolVersion where
    arbitrary = ProtocolVersion <$> arbitrary <*> arbitrary

testBuiltinVersions :: TestTree
testBuiltinVersions = testGroup "builtins"
    [ testCase "all builtins are available some time" $
            let allPvBuiltins = fold $ Map.elems builtinsIntroducedIn
                allBuiltins = enumerate @DefaultFun
            in for_ allBuiltins $ \f -> assertBool (show f) (f `Set.member` allPvBuiltins)
    , testCase "builtins aren't available before Alonzo" $
        assertBool "empty" (Set.null $ builtinsAvailableIn PlutusV1 maryPV)
    , testCase "serializeData is only available in l2,Vasil and after" $ do
         assertBool "in l1,Alonzo" $ isLeft $ V1.assertScriptWellFormed alonzoPV serialiseDataExScript
         assertBool "in l1,Vasil" $ isLeft $ V1.assertScriptWellFormed vasilPV serialiseDataExScript
         assertBool "in l2,Alonzo" $ isLeft $ V2.assertScriptWellFormed alonzoPV serialiseDataExScript
         assertBool "in l3,Alonzo" $ isLeft $ V3.assertScriptWellFormed alonzoPV serialiseDataExScript
         assertBool "not in l2,Vasil" $ isRight $ V2.assertScriptWellFormed vasilPV serialiseDataExScript
         assertBool "not in l3,future" $ isRight $ V3.assertScriptWellFormed futurePV serialiseDataExScript
    , testCase "bls,keccak256,blake2b224 only available in l3,Future and after" $
         for_ [blsExScript, keccak256ExScript, blake2b224ExScript] $ \script -> do
             assertBool "in l1,Alonzo" $ isLeft $ V1.assertScriptWellFormed alonzoPV script
             assertBool "in l1,Vasil" $ isLeft $ V1.assertScriptWellFormed vasilPV script
             assertBool "in l2,Alonzo" $ isLeft $ V2.assertScriptWellFormed alonzoPV script
             assertBool "in l3,Alonzo" $ isLeft $ V3.assertScriptWellFormed alonzoPV script
             assertBool "in l2,Valentine" $ isLeft $ V2.assertScriptWellFormed valentinePV script
             assertBool "not in l3,future" $ isRight $ V3.assertScriptWellFormed futurePV script
    ]

testRmdr :: TestTree
testRmdr = testGroup "rmdr"
    [ testCase "remdr" $ do
         assertBool "remdr1" $ isRight $ V1.assertScriptWellFormed valentinePV $ errorScript <> "remdr1"
         assertBool "remdr2" $ isRight $ V2.assertScriptWellFormed valentinePV $ errorScript <> "remdr2"
         assertBool "remdr1c" $ isRight $ V1.assertScriptWellFormed conwayPV $ errorScript <> "remdr1"
         assertBool "remdr2c" $ isRight $ V2.assertScriptWellFormed conwayPV $ errorScript <> "remdr2"
         assertEqual "remdr3" (Left $ RemainderError "remdr3") $ V3.assertScriptWellFormed conwayPV $ errorScript <> "remdr3"
    , testProperty "remdr1gen"$ \remdr -> isRight $ V1.assertScriptWellFormed valentinePV $ errorScript <> BSS.pack remdr
    , testProperty "remdr2gen"$ \remdr -> isRight $ V2.assertScriptWellFormed valentinePV $ errorScript <> BSS.pack remdr
    , testProperty "remdr1genc"$ \remdr -> isRight $ V1.assertScriptWellFormed conwayPV $ errorScript <> BSS.pack remdr
    , testProperty "remdr2genc"$ \remdr -> isRight $ V2.assertScriptWellFormed conwayPV $ errorScript <> BSS.pack remdr
    -- we cannot make the same property as above for remdr3gen because it may generate valid bytestring append extensions to the original script
    -- a more sophisticated one could work though
    ]

-- See Note [Checking the Plutus Core language version] for why these have to use mkTermToEvaluate
testLanguageVersions :: TestTree
testLanguageVersions = testGroup "Plutus Core language versions"
  [ testCase "v1.1.0 is available in l3,future and not before" $ do
      assertBool "in l3,Vasil" $ isLeft $ mkTermToEvaluate PlutusV3 vasilPV v110script []
      assertBool "in l2,future" $ isLeft $ mkTermToEvaluate PlutusV2 conwayPV v110script []
      assertBool "not in l3,future" $ isRight $ mkTermToEvaluate PlutusV3 conwayPV v110script []
  , testCase "constr is not available with v1.0.0 ever" $ assertBool "in l3,future" $ isLeft $ mkTermToEvaluate PlutusV3 conwayPV badConstrScript []
  , testCase "case is not available with v1.0.0 ever" $ assertBool "in l3,future" $ isLeft $ mkTermToEvaluate PlutusV3 conwayPV badCaseScript []
  ]

-- * UPLC written examples to test

serialiseDataExScript :: SerialisedScript
serialiseDataExScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $
    UPLC.Apply () (UPLC.Builtin () PLC.SerialiseData) (PLC.mkConstant () $ I 1)

errorScript :: SerialisedScript
errorScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $ UPLC.Error ()

v110script :: SerialisedScript
v110script = serialiseUPLC $ UPLC.Program () PLC.plcVersion110 $ UPLC.Constr () 0 []

badConstrScript :: SerialisedScript
badConstrScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $ UPLC.Constr () 0 []

badCaseScript :: SerialisedScript
badCaseScript = serialiseUPLC $ UPLC.Program () PLC.plcVersion100 $ UPLC.Case () (UPLC.Error ()) []

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
