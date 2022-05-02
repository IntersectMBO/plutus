module Spec.Builtins where

import Plutus.V1.Ledger.Api qualified as V1
import Plutus.V1.Ledger.Scripts
import Plutus.V2.Ledger.Api qualified as V2
import PlutusCore as PLC
import PlutusCore.Data as PLC
import PlutusCore.MkPlc as PLC
import UntypedPlutusCore as UPLC

import Codec.Serialise
import Data.ByteString.Lazy as BSL
import Data.ByteString.Short
import Data.Foldable (fold, for_)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Plutus.ApiCommon as Common
import Test.Tasty
import Test.Tasty.HUnit

serialiseDataExScript :: SerializedScript
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
    , testCase "builtins aren't available before p5" $ assertBool "empty" (Set.null $ builtinsAvailableIn PlutusV1 (p 4)) -- l1 valid, p4 invalid
    , testCase "serializeData is only available in l2,p6 and after" $ do
         assertBool "in l1,p5" $ not $ V1.isScriptWellFormed (p 5) serialiseDataExScript
         assertBool "in l1,p6" $ not $ V1.isScriptWellFormed (p 6) serialiseDataExScript
         assertBool "in l2,p5" $ not $ V2.isScriptWellFormed (p 5) serialiseDataExScript
         assertBool "not in l2,p6" $ V2.isScriptWellFormed (p 6) serialiseDataExScript
    , testCase "cost model parameters " $
         -- v1 is missing some cost model parameters because new builtins are added in v2
         assertBool "v1 params is proper subset of v2 params" $ V1.costModelParamNames `Set.isProperSubsetOf` V2.costModelParamNames
    ]
  where
    p x = ProtocolVersion x 0
