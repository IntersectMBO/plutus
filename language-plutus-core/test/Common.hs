{-# LANGUAGE DerivingStrategies #-}
module Common
    ( TestNestedGolden
    , runTestNestedGoldenIn
    , testNestedGolden
    , goldenVsText
    , goldenVsDoc
    , nestedGoldenVsText
    , nestedGoldenVsDoc
    ) where

import           Language.PlutusCore.Pretty

import           Control.Monad.Reader       (Reader)
import qualified Control.Monad.Reader       as Reader
import qualified Data.ByteString.Lazy       as BSL
import           Data.Text                  (Text)
import           Data.Text.Encoding         (encodeUtf8)
import           System.FilePath            ((</>))
import           Test.Tasty
import           Test.Tasty.Golden

-- | A 'TestTree' of golden tests stored in some folder.
type TestNestedGolden = Reader (String -> FilePath) TestTree

-- | Run a 'TestTree' of golden tests against a folder.
runTestNestedGoldenIn :: FilePath -> TestNestedGolden -> TestTree
runTestNestedGoldenIn folder test = Reader.runReader test (</> folder)

-- | Descend into a folder of golden tests.
testNestedGolden :: String -> [TestNestedGolden] -> TestNestedGolden
testNestedGolden folderName =
    Reader.local ((</> folderName ) .) . fmap (testGroup folderName) . sequence

-- | Check the contents of a file against a 'Text'.
goldenVsText :: TestName -> FilePath -> Text -> TestTree
goldenVsText name ref = goldenVsString name ref . pure . BSL.fromStrict . encodeUtf8

-- | Check the contents of a file against a 'Doc'.
goldenVsDoc :: TestName -> FilePath -> Doc ann -> TestTree
goldenVsDoc name ref = goldenVsText name ref . docText

-- | Check the contents of a file nested in some folder against a 'Text'.
nestedGoldenVsText :: TestName -> Text -> TestNestedGolden
nestedGoldenVsText name text = do
    toFolder <- Reader.ask
    return $ goldenVsText name (toFolder "" </> name ++ ".plc.golden") text

-- | Check the contents of a file nested in some folder against a 'Text'.
nestedGoldenVsDoc :: TestName -> Doc ann -> TestNestedGolden
nestedGoldenVsDoc name = nestedGoldenVsText name . docText
