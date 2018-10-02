module Pretty.Readable (test_PrettyReadable) where

import           Language.PlutusCore.Pretty
import           Language.PlutusCore.StdLib.Everything

import           Common

import           Test.Tasty

testReadable :: PrettyPlc a => TestName -> a -> TestNestedGolden
testReadable name
    = nestedGoldenVsDoc name
    . prettyPlcReadableBy (botPrettyConfigReadable defPrettyConfigName)

test_PrettyReadable :: TestTree
test_PrettyReadable =
    runTestNestedGoldenIn ["test", "Pretty", "Golden", "Readable"] $
        foldStdLib testNestedGolden testReadable testReadable
