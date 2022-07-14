-- editorconfig-checker-disable-file
{-# LANGUAGE TypeApplications #-}
module Spec.Builtins where

import PlutusCore as PLC
import PlutusCore.Data as PLC
import PlutusCore.MkPlc as PLC
import PlutusLedgerApi.Common
import PlutusLedgerApi.Common.Versions
import PlutusLedgerApi.V1 qualified as V1
import PlutusLedgerApi.V1.Scripts
import PlutusLedgerApi.V2 qualified as V2
import PlutusLedgerApi.V3 qualified as V3
import UntypedPlutusCore as UPLC

import Codec.Serialise
import Data.ByteString.Lazy as BSL
import Data.ByteString.Short
import Data.Foldable (fold, for_)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Test.Tasty
import Test.Tasty.HUnit

serialiseDataExScript :: SerialisedScript
serialiseDataExScript = toShort . toStrict $ serialise serialiseDataEx
    where
      serialiseDataEx :: Script
      serialiseDataEx = Script $ UPLC.Program () (PLC.defaultVersion ()) $
                             UPLC.Apply () (UPLC.Builtin () PLC.SerialiseData) (PLC.mkConstant () $ I 1)

tests :: TestTree
tests =
  testGroup
    "builtins"
    [ testCase "all builtins are available some time" $
            let allPvBuiltins = fold $ Map.elems builtinsIntroducedIn
                allBuiltins = [(toEnum 0)..]
            in for_ allBuiltins $ \f -> assertBool (show f) (f `Set.member` allPvBuiltins)
    , testCase "builtins aren't available before Alonzo" $ assertBool "empty" (Set.null $ builtinsAvailableIn PlutusV1 maryPV) -- l1 valid, p4 invalid
    , testCase "serializeData is only available in l2,Vasil and after" $ do
         assertBool "in l1,Alonzo" $ not $ V1.isScriptWellFormed alonzoPV serialiseDataExScript
         assertBool "in l1,Vasil" $ not $ V1.isScriptWellFormed vasilPV serialiseDataExScript
         assertBool "in l2,Alonzo" $ not $ V2.isScriptWellFormed alonzoPV serialiseDataExScript
         assertBool "in l3,Alonzo" $ not $ V3.isScriptWellFormed alonzoPV serialiseDataExScript
         assertBool "not in l2,Vasil" $ V2.isScriptWellFormed vasilPV serialiseDataExScript
         assertBool "not in l3,Chang" $ V3.isScriptWellFormed changPV serialiseDataExScript
    ]
