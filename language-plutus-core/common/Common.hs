module Common
    ( TestNested
    , runTestNestedIn
    , testNested
    , goldenVsText
    , goldenVsDoc
    , nestedGoldenVsText
    , nestedGoldenVsDoc
    ) where

import           Language.PlutusCore.Pretty

import           Control.Monad.Reader       (Reader, runReader)
import qualified Control.Monad.Reader       as Reader
import qualified Data.ByteString.Lazy       as BSL
import           Data.Text                  (Text)
import           Data.Text.Encoding         (encodeUtf8)
import           System.FilePath            ((</>))
import           Test.Tasty
import           Test.Tasty.Golden

-- | A 'TestTree' of tests stored in some folder.
type TestNested = Reader [String] TestTree

-- | Run a 'TestTree' of tests against a folder.
runTestNestedIn :: [String] -> TestNested -> TestTree
runTestNestedIn path test = runReader test path

-- | Descend into a folder of tests.
testNested :: String -> [TestNested] -> TestNested
testNested folderName =
    Reader.local (++ [folderName]) . fmap (testGroup folderName) . sequence

-- | Check the contents of a file against a 'Text'.
goldenVsText :: TestName -> FilePath -> IO Text -> TestTree
goldenVsText name ref val = goldenVsString name ref $ BSL.fromStrict . encodeUtf8 <$> val

-- | Check the contents of a file against a 'Doc'.
goldenVsDoc :: TestName -> FilePath -> IO (Doc ann) -> TestTree
goldenVsDoc name ref val = goldenVsText name ref $ docText <$> val

-- | Check the contents of a file nested in some folder against a 'Text'.
nestedGoldenVsText :: TestName -> IO Text -> TestNested
nestedGoldenVsText name text = do
    path <- Reader.ask
    return $ goldenVsText name (foldr (</>) (name ++ ".plc.golden") path) text

-- | Check the contents of a file nested in some folder against a 'Text'.
nestedGoldenVsDoc :: TestName -> IO (Doc ann) -> TestNested
nestedGoldenVsDoc name val = nestedGoldenVsText name $ docText <$> val
