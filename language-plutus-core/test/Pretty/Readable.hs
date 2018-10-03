module Pretty.Readable (test_PrettyReadable) where

import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Quote
import           Language.PlutusCore.StdLib.Everything

import           Common

import           Test.Tasty

prettyConfigReadable :: PrettyConfigPlc
prettyConfigReadable
    = PrettyConfigPlc defPrettyConfigPlcOptions
    . PrettyConfigPlcReadable
    $ botPrettyConfigReadable defPrettyConfigName

testReadable :: PrettyPlc a => TestName -> Quote a -> TestNestedGolden
testReadable name = nestedGoldenVsDoc name . prettyBy prettyConfigReadable . runQuote

test_PrettyReadable :: TestTree
test_PrettyReadable =
    runTestNestedGoldenIn ["test", "Pretty", "Golden", "Readable"] $
        foldStdLib testNestedGolden testReadable testReadable
