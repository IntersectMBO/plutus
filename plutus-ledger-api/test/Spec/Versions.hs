-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Spec.Versions (tests) where

import PlutusCore as PLC
import PlutusCore.Data as PLC
import PlutusCore.MkPlc as PLC
import PlutusLedgerApi.Common
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3 qualified as V3
import PlutusPrelude
import UntypedPlutusCore as UPLC

import Control.Monad.Except
import Data.ByteString.Short as BSS
import Data.Either
import Data.Foldable (for_)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

serialiseDataExScript :: SerialisedScript
serialiseDataExScript = serialiseUPLC serialiseDataEx
    where
      serialiseDataEx = UPLC.Program () (PLC.defaultVersion ()) $
                             UPLC.Apply () (UPLC.Builtin () PLC.SerialiseData) (PLC.mkConstant () $ I 1)

errorScript :: SerialisedScript
errorScript = serialiseUPLC errorEx
    where
      errorEx = UPLC.Program () (PLC.defaultVersion ()) $ UPLC.Error ()

tests :: TestTree
tests = testGroup "versions"
    [ testLangVersions
    , testBuiltinVersions
    ]

testLangVersions :: TestTree
testLangVersions = testGroup "langs"
    [ testProperty "v1 not before but after" $ prop_notBeforeButAfter V1.assertScriptWellFormed AlonzoPV
    , testProperty "v2 not before but after" $ prop_notBeforeButAfter V2.assertScriptWellFormed VasilPV
    , testProperty "v3 not before but after" $ prop_notBeforeButAfter V3.assertScriptWellFormed ChangPV
    , testProperty "protocol-versions can add but not remove language versions" $
        \pvA pvB -> pvA < pvB ==> languagesAvailableIn pvA `Set.isSubsetOf` languagesAvailableIn pvB
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
                   Left LanguageNotAvailableError{} -> True
                   _                                -> False
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
    , testCase "builtins aren't available before Alonzo" $ assertBool "empty" (Set.null $ builtinsAvailableIn PlutusV1 MaryPV) -- l1 valid, p4 invalid
    , testCase "serializeData is only available in l2,Vasil and after" $ do
         assertBool "in l1,Alonzo" $ isLeft $ V1.assertScriptWellFormed AlonzoPV serialiseDataExScript
         assertBool "in l1,Vasil" $ isLeft $ V1.assertScriptWellFormed VasilPV serialiseDataExScript
         assertBool "in l2,Alonzo" $ isLeft $ V2.assertScriptWellFormed AlonzoPV serialiseDataExScript
         assertBool "in l3,Alonzo" $ isLeft $ V3.assertScriptWellFormed AlonzoPV serialiseDataExScript
         assertBool "not in l2,Vasil" $ isRight $ V2.assertScriptWellFormed VasilPV serialiseDataExScript
         assertBool "not in l3,Chang" $ isRight $ V3.assertScriptWellFormed ChangPV serialiseDataExScript
         assertBool "remdr1" $ isRight $ V1.assertScriptWellFormed ChangPV $ errorScript <> "remdr1"
         assertBool "remdr2" $ isRight $ V2.assertScriptWellFormed ChangPV $ errorScript <> "remdr2"
         assertEqual "remdr3" (Left $ RemainderError "remdr3") $ V3.assertScriptWellFormed ChangPV $ errorScript <> "remdr3"
    , testProperty "remdr1gen"$ \remdr -> isRight $ V1.assertScriptWellFormed ChangPV $ errorScript <> BSS.pack remdr
    , testProperty "remdr2gen"$ \remdr -> isRight $ V2.assertScriptWellFormed ChangPV $ errorScript <> BSS.pack remdr
    -- we cannot make the same property as above for remdr3gen because it may generate valid bytestring append extensions to the original script
    -- a more sophisticated one could work though
    ]
