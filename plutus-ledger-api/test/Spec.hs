module Main(main) where

import           Test.Tasty
import           Test.Tasty.HUnit

import           Data.Either
import           Data.Maybe
import           Plutus.V1.Ledger.Api
import           Plutus.V1.Ledger.Examples
import qualified Spec.Interval

main :: IO ()
main = defaultMain tests

alwaysTrue :: TestTree
alwaysTrue = testCase "always true script returns true" $
    let (_, res) = evaluateScriptCounting Quiet (fromJust defaultCostModelParams) (alwaysSucceedingNAryFunction 2) [I 1, I 2]
    in assertBool "succeeds" (isRight res)

alwaysFalse :: TestTree
alwaysFalse = testCase "always false script returns false" $
    let (_, res) = evaluateScriptCounting Quiet (fromJust defaultCostModelParams) (alwaysFailingNAryFunction 2) [I 1, I 2]
    in assertBool "fails" (isLeft res)

tests :: TestTree
tests = testGroup "plutus-ledger-api" [
    alwaysTrue
    , alwaysFalse
    , Spec.Interval.tests
    ]
