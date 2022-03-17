module Spec.Builtins where

import Plutus.V1.Ledger.Api
import Plutus.V1.Ledger.Scripts as Scripts
import PlutusCore as PLC
import PlutusCore.MkPlc as PLC
import UntypedPlutusCore as UPLC

import Codec.Serialise
import Data.ByteString.Lazy as BSL
import Data.ByteString.Short
import Data.Foldable (fold, for_)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Plutus.ApiCommon
import Test.Tasty
import Test.Tasty.HUnit

serialiseDataExScript :: SerializedScript
serialiseDataExScript = toShort . toStrict $ serialise serialiseDataEx
    where
      serialiseDataEx :: Script
      serialiseDataEx = Scripts.Script $ UPLC.Program () (PLC.defaultVersion ()) $
                             UPLC.Apply () (UPLC.Builtin () PLC.SerialiseData) (PLC.mkConstant () $ I 1)

tests :: TestTree
tests =
  testGroup
    "builtins"
    [ testCase "all builtins are available some time" $
            let allPvBuiltins = fold $ Map.elems $ builtinsIntroducedIn
                allBuiltins = [(toEnum 0)..]
            in for_ allBuiltins $ \f -> assertBool (show f) (f `Set.member` allPvBuiltins)
    , testCase "builtins aren't available before v5" $ assertBool "empty" (Set.null $ builtinsAvailableIn (ProtocolVersion 4 0))
    , testCase "serializeData is only available in v6" $ do
         assertBool "in v5 " $ not $ isScriptWellFormed (ProtocolVersion 5 0) serialiseDataExScript
         assertBool "not in v6" $ isScriptWellFormed (ProtocolVersion 6 0) serialiseDataExScript
    ]
