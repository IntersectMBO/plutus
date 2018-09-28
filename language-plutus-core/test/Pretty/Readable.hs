module Pretty.Readable (test_PrettyReadable) where

import           Language.PlutusCore
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.ChurchNat
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Data.Unit

import           Control.Monad.Reader                      (Reader)
import qualified Control.Monad.Reader                      as Reader
import qualified Data.ByteString.Lazy                      as BSL
import           Data.Text                                 (Text)
import           Data.Text.Encoding                        (encodeUtf8)
import           System.FilePath                           ((</>))
import           Test.Tasty
import           Test.Tasty.Golden

goldenVsText :: TestName -> FilePath -> Text -> TestTree
goldenVsText name ref = goldenVsString name ref . pure . BSL.fromStrict . encodeUtf8

type TestFolder = Reader (String -> FilePath) TestTree

checkPlcReadable :: PrettyPlc a => TestName -> a -> TestFolder
checkPlcReadable name x = do
    toFolder <- Reader.ask
    return
       . goldenVsText name (toFolder "" </> name ++ ".plc.golden")
       $ docText (prettyPlcReadableBy (botPrettyConfigReadable defPrettyConfigName) x)

testFolder :: String -> [TestFolder] -> TestFolder
testFolder folderName = Reader.local ((</> folderName ) .) . fmap (testGroup folderName) . sequence

runTestFolderIn :: FilePath -> TestFolder -> TestTree
runTestFolderIn folder test = Reader.runReader test (</> folder)

test_PrettyReadable :: TestTree
test_PrettyReadable =
    runTestFolderIn "test/Pretty/Golden/Readable" $
        testFolder "StdLib"
            [ testFolder "Bool"
                  [ checkPlcReadable "Bool"  $ runQuote getBuiltinBool
                  , checkPlcReadable "True"  $ runQuote getBuiltinTrue
                  , checkPlcReadable "False" $ runQuote getBuiltinFalse
                  , checkPlcReadable "If"    $ runQuote getBuiltinIf
                  ]
            , testFolder "ChurchNat"
                  [ checkPlcReadable "ChurchNat"  $ runQuote getBuiltinChurchNat
                  , checkPlcReadable "ChurchZero" $ runQuote getBuiltinChurchZero
                  , checkPlcReadable "ChurchSucc" $ runQuote getBuiltinChurchSucc
                  ]
            , testFolder "Function"
                  [ checkPlcReadable "Const"  $ runQuote getBuiltinConst
                  -- , checkPlcReadable "Self"   $ runQuote getBuiltinSelf
                  , checkPlcReadable "Unroll" $ runQuote getBuiltinUnroll
                  , checkPlcReadable "Fix"    $ runQuote getBuiltinFix
                  ]
            , testFolder "List"
                  [ -- checkPlcReadable "List"      $ runQuote getBuiltinList
                    checkPlcReadable "Nil"       $ runQuote getBuiltinNil
                  , checkPlcReadable "Cons"      $ runQuote getBuiltinCons
                  , checkPlcReadable "FoldrList" $ runQuote getBuiltinFoldrList
                  , checkPlcReadable "FoldList"  $ runQuote getBuiltinFoldList
                  ]
            , testFolder "Nat"
                  [ -- checkPlcReadable "Nat"      $ runQuote getBuiltinNat
                    checkPlcReadable "Zero"     $ runQuote getBuiltinZero
                  , checkPlcReadable "Succ"     $ runQuote getBuiltinSucc
                  , checkPlcReadable "FoldrNat" $ runQuote getBuiltinFoldrNat
                  , checkPlcReadable "FoldNat"  $ runQuote getBuiltinFoldNat
                  ]
            , testFolder "Unit"
                  [ checkPlcReadable "Unit"    $ runQuote getBuiltinUnit
                  , checkPlcReadable "Unitval" $ runQuote getBuiltinUnitval
                  ]
            ]
