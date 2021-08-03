module Main
    ( main
    ) where

import qualified Plutus.PAB.CliSpec
import qualified Plutus.PAB.CoreSpec
import qualified Plutus.PAB.Effects.Contract.BuiltinSpec
import           Test.Tasty                              (defaultMain, testGroup)

main :: IO ()
main =
    defaultMain $
    testGroup
        "all tests"
        [ Plutus.PAB.CoreSpec.tests
        , Plutus.PAB.CliSpec.tests
        , Plutus.PAB.Effects.Contract.BuiltinSpec.tests
        ]
