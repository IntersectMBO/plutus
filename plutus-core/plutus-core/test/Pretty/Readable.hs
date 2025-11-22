module Pretty.Readable (test_Pretty) where

import PlutusCore.Default
import PlutusCore.FsTree
import PlutusCore.Pretty

import PlutusCore.Examples.Everything (examples)
import PlutusCore.StdLib.Everything (stdLib)

import Data.Default.Class

import Test.Tasty.Extras

import Test.Tasty

prettyConfigReadable :: PrettyConfigPlc
prettyConfigReadable =
  PrettyConfigPlc prettyConfigPlcOptions
    . PrettyConfigPlcReadable
    $ botPrettyConfigReadable prettyConfigNameSimple def

testReadable :: PrettyPlc a => TestName -> a -> TestNested
testReadable name = nestedGoldenVsDoc name "" . prettyBy prettyConfigReadable

test_PrettyReadable :: TestTree
test_PrettyReadable =
  testGroup
    "Bundles"
    [ folder stdLib
    , folder examples
    ]
  where
    folder :: Pretty fun => PlcFolderContents DefaultUni fun -> TestTree
    folder =
      runTestNested ["plutus-core", "test", "Pretty", "Golden", "Readable"]
        . foldPlcFolderContents testNested testReadable testReadable

test_Pretty :: TestTree
test_Pretty =
  testGroup
    "pretty"
    [ test_PrettyReadable
    ]
