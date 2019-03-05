module Main (main) where

import qualified Lift.Spec   as Lift
import qualified Map.Spec    as Map
import qualified Plugin.Spec as Plugin
import qualified TH.Spec     as TH

import           Common

import           Test.Tasty

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "tests" [
      runTestNestedIn ["test"] $ testGroup "tests" <$> sequence [
          Plugin.tests
        , Lift.tests
        , TH.tests
      ]
      , Map.tests
    ]
