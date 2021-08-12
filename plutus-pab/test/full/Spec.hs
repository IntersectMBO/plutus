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
        [
        Plutus.PAB.CoreSpec.tests
        -- TODO: To be re-instated once we resolve big delays experienced by
        -- running lots of PABs at once.
        -- , Plutus.PAB.CliSpec.tests
        , Plutus.PAB.Effects.Contract.BuiltinSpec.tests
        ]
