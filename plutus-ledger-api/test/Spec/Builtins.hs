module Spec.Builtins where

import Data.Foldable (fold, for_)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Plutus.ApiCommon
import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests =
  testGroup
    "builtins"
    [ testCase "all builtins are available some time" $
            let allPvBuiltins = fold $ Map.elems $ builtinsIntroducedIn
                allBuiltins = [(toEnum 0)..]
            in for_ allBuiltins $ \f -> assertBool (show f) (f `Set.member` allPvBuiltins)
    , testCase "builtins aren't available before v5" $ assertBool "empty" (Set.null $ builtinsAvailableIn (ProtocolVersion 4 0))
    ]
