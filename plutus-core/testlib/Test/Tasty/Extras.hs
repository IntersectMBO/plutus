{-# LANGUAGE TupleSections #-}

module Test.Tasty.Extras
    ( TestNested
    , TestNestedM
    , runTestNestedIn
    , runTestNested
    , testNestedM
    , testNestedGhcM
    , listNested
    , testNested
    , testNestedGhc
    , goldenVsText
    , goldenVsTextM
    , goldenVsDoc
    , goldenVsDocM
    , nestedGoldenVsText
    , nestedGoldenVsTextM
    , nestedGoldenVsDoc
    , nestedGoldenVsDocM
    , makeVersionedFilePath
    ) where

import PlutusPrelude

import Control.Monad.Free.Church (F (runF), liftF)
import Control.Monad.Reader
import Data.ByteString.Lazy qualified as BSL
import Data.Functor.Identity
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import Data.Version
import System.FilePath (joinPath, (</>))
import System.Info
import Test.Tasty
import Test.Tasty.Golden

-- | We use the GHC version number to create directories with names like `9.2`
-- and `9.6` containing golden files whose contents depend on the GHC version.
-- For consistency all such directories should be leaves in the directory
-- hierarchy: for example, it is preferable to have golden files in
-- "semantics/9.2/" instead of "9.2/semantics/".
ghcVersion :: String
ghcVersion = showVersion compilerVersion

{- Note [OS-independent paths].  Some of the functions here take arguments of the
   form [FilePath].  The intention is that the members of the list should be
   simple directory names containing no OS-dependent separators (eg ["dir",
   "subdir"], but not ["dir/subdir"]).  The components of the path will be
   concatenated with appropriate separators by means of `joinPath`.
-}

-- | Given a lists of FilePaths and a filename, concatenate the members of the
-- list together, append the GHC version number, then append the filename.  We
-- use this to create GHC-version-dependent golden files.
makeVersionedFilePath :: [FilePath] -> FilePath -> FilePath
makeVersionedFilePath path file = joinPath path </> ghcVersion </> file

type TestNestedT = ReaderT [FilePath]

-- | A 'TestTree' of tests under some name prefix.
type TestNested = TestNestedT Identity TestTree

type TestNestedM = TestNestedT (F ((,) TestTree))

blah = runTestNested $ testNestedM "abc" $ do
    testNestedM "def" $ do
        pure ()
    testNestedM "ghi" $ do
        pure ()

-- | Run a 'TestTree' of tests with a given name prefix. This doesn't actually run the tests:
-- instead it runs a computation in the Reader monad.
runTestNestedIn :: [FilePath] -> TestNested -> TestTree
runTestNestedIn path test = runReader test path

-- | Run a 'TestTree' of tests with an empty prefix. This doesn't actually run the tests: instead it
-- runs a computation in the Reader monad.
runTestNested :: TestNested -> TestTree
runTestNested = runTestNestedIn []

-- | Descend into a folder.
testNestedM :: FilePath -> TestNestedM () -> TestNested
testNestedM folderName
    = local (++ [folderName])
    . fmap (testGroup folderName)
    . mapReaderT (\tests -> pure . runF tests mempty $ uncurry (:))

-- | Like 'testNestedM' but adds a subdirectory corresponding to the GHC version being used.
testNestedGhcM :: TestNestedM () -> TestNested
testNestedGhcM = testNestedM ghcVersion

listNested :: [TestNested] -> TestNestedM ()
listNested = traverse_ . mapReaderT $ liftF . (, ()) . runIdentity

testNested :: FilePath -> [TestNested] -> TestNested
testNested folderName = testNestedM folderName . listNested

-- | Like 'testNestedM' but adds a subdirectory corresponding to the GHC version being used.
testNestedGhc :: [TestNestedM ()] -> TestNested
testNestedGhc = testNestedM ghcVersion . listNested

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
nestedGoldenVsText :: TestName -> FilePath -> Text -> TestNestedM ()
nestedGoldenVsText name ext = nestedGoldenVsTextM name ext . pure

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsTextM :: TestName -> FilePath -> IO Text -> TestNestedM ()
nestedGoldenVsTextM name ext text = do
    path <- ask
    -- TODO: make more generic
    return $ goldenVsTextM name (foldr (</>) (name ++ ext ++ ".golden") path) text

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsDoc :: TestName -> FilePath -> Doc ann -> TestNestedM ()
nestedGoldenVsDoc name ext = nestedGoldenVsDocM name ext . pure

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsDocM :: TestName -> FilePath -> IO (Doc ann) -> TestNestedM ()
nestedGoldenVsDocM name ext val = nestedGoldenVsTextM name ext $ render <$> val
