module Pretty.Readable (test_Pretty) where

import           Language.PlutusCore.FsTree              (foldPlcFolderContents)
import           Language.PlutusCore.Pretty

import           Language.PlutusCore.Examples.Everything (examples)
import           Language.PlutusCore.StdLib.Everything   (stdLib)

import           Common

import           Test.Tasty

prettyConfigReadable :: PrettyConfigPlc
prettyConfigReadable
    = PrettyConfigPlc defPrettyConfigPlcOptions
    . PrettyConfigPlcReadable
    $ botPrettyConfigReadable defPrettyConfigName ShowKindsYes

testReadable :: PrettyPlc a => TestName -> a -> TestNested
testReadable name = nestedGoldenVsDoc name . prettyBy prettyConfigReadable

test_PrettyReadable :: TestTree
test_PrettyReadable
    = runTestNestedIn ["test", "Pretty", "Golden"]
    . testNested "Readable"
    . foldPlcFolderContents testNested testReadable testReadable
    $ stdLib <> examples

test_Pretty :: TestTree
test_Pretty =
    testGroup "pretty"
        [ test_PrettyReadable
        ]
