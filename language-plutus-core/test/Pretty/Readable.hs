module Pretty.Readable (test_Pretty) where

import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Everything

import           Common

import           Test.Tasty

prettyConfigReadable :: PrettyConfigPlc
prettyConfigReadable
    = PrettyConfigPlc defPrettyConfigPlcOptions
    . PrettyConfigPlcReadable
    $ botPrettyConfigReadable defPrettyConfigName True

testReadable :: PrettyPlc a => TestName -> Quote a -> TestNested
testReadable name = nestedGoldenVsDoc name . prettyBy prettyConfigReadable . runQuote

test_PrettyReadable :: TestTree
test_PrettyReadable =
    runTestNestedIn ["test", "Pretty", "Golden", "Readable"] $
        foldStdLib testNested testReadable testReadable

test_Pretty :: TestTree
test_Pretty =
    testGroup "pretty"
        [ test_PrettyReadable
        ]
