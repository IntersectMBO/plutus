module Main
    ( main
    ) where

import qualified GistSpec
import qualified Playground.InterpreterSpec
import qualified Playground.UsecasesSpec
import           Test.Tasty                 (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
    testGroup
        "all tests"
        [ GistSpec.tests
        , Playground.UsecasesSpec.tests
        , Playground.InterpreterSpec.tests
        ]
