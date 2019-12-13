module Main
    ( main
    ) where

import qualified Playground.THSpec
import qualified Playground.TypesSpec
import qualified SchemaSpec
import           Test.Tasty           (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
    testGroup
        "all tests"
        [SchemaSpec.tests, Playground.THSpec.tests, Playground.TypesSpec.tests]
