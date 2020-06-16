module Main
    ( main
    ) where

import qualified Auth.TypesSpec
import qualified Playground.THSpec
import qualified Playground.TypesSpec
import qualified SchemaSpec
import           Test.Tasty           (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
    testGroup
        "all tests"
        [ Auth.TypesSpec.tests
        , SchemaSpec.tests
        , Playground.THSpec.tests
        , Playground.TypesSpec.tests
        ]
