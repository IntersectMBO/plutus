module Main
    ( main
    ) where

import qualified GistSpec
import qualified Playground.Rollup.RenderSpec
import qualified Playground.UsecasesSpec
import           Test.Tasty                   (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
    testGroup
        "all tests"
        [ GistSpec.tests
        , Playground.Rollup.RenderSpec.tests
        , Playground.UsecasesSpec.tests
        ]
