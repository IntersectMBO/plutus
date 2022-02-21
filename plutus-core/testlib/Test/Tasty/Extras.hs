module Test.Tasty.Extras
    ( TestNested
    , runTestNestedIn
    , runTestNested
    , testNested
    , goldenVsText
    , goldenVsTextM
    , goldenVsDoc
    , goldenVsDocM
    , nestedGoldenVsText
    , nestedGoldenVsTextM
    , nestedGoldenVsDoc
    , nestedGoldenVsDocM
    , topSourcePos
    ) where

import PlutusPrelude

import Control.Monad.Reader
import Data.ByteString.Lazy qualified as BSL
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import PlutusCore (topSourcePos)
import System.FilePath ((</>))
import Test.Tasty
import Test.Tasty.Golden

-- | A 'TestTree' of tests under some name prefix.
type TestNested = Reader [String] TestTree

-- | Run a 'TestTree' of tests with a given name prefix.
runTestNestedIn :: [String] -> TestNested -> TestTree
runTestNestedIn path test = runReader test path

-- | Run a 'TestTree' of tests with an empty prefix.
runTestNested :: TestNested -> TestTree
runTestNested = runTestNestedIn []

-- | Descend into a name prefix.
testNested :: String -> [TestNested] -> TestNested
testNested folderName =
    local (++ [folderName]) . fmap (testGroup folderName) . sequence

-- | Check the contents of a file against a 'Text'.
goldenVsText :: TestName -> FilePath -> Text -> TestTree
goldenVsText name ref = goldenVsTextM name ref . pure

-- | Check the contents of a file against a 'Text'.
goldenVsTextM :: TestName -> FilePath -> IO Text -> TestTree
goldenVsTextM name ref val =
    goldenVsStringDiff name (\expected actual -> ["diff", "-u", expected, actual]) ref $
    BSL.fromStrict . encodeUtf8 <$> val

-- | Check the contents of a file against a 'Doc'.
goldenVsDoc :: TestName -> FilePath -> Doc ann -> TestTree
goldenVsDoc name ref = goldenVsDocM name ref . pure

-- | Check the contents of a file against a 'Doc'.
goldenVsDocM :: TestName -> FilePath -> IO (Doc ann) -> TestTree
goldenVsDocM name ref val = goldenVsTextM name ref $ render <$> val

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsText :: TestName -> Text -> TestNested
nestedGoldenVsText name = nestedGoldenVsTextM name . pure

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsTextM :: TestName -> IO Text -> TestNested
nestedGoldenVsTextM name text = do
    path <- ask
    -- TODO: make more generic
    return $ goldenVsTextM name (foldr (</>) (name ++ ".plc.golden") path) text

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsDoc :: TestName -> Doc ann -> TestNested
nestedGoldenVsDoc name = nestedGoldenVsDocM name . pure

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsDocM :: TestName -> IO (Doc ann) -> TestNested
nestedGoldenVsDocM name val = nestedGoldenVsTextM name $ render <$> val
