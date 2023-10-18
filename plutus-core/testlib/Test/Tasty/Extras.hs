module Test.Tasty.Extras
    ( TestNested
    , runTestNestedIn
    , runTestNested
    , testNested
    , testNestedGhc
    , runTestGroupNestedGhc
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

import Control.Monad.Reader
import Data.ByteString.Lazy qualified as BSL
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

-- | A 'TestTree' of tests under some name prefix.
type TestNested = Reader [FilePath] TestTree

-- | Run a 'TestTree' of tests with a given name prefix.  This doesn't actually
-- run the tests: instead it runs a computation in the Reader monad.
runTestNestedIn :: [FilePath] -> TestNested -> TestTree
runTestNestedIn path test = runReader test path

-- | Run a 'TestTree' of tests with an empty prefix.  This doesn't actually run
-- the tests: instead it runs a computation in the Reader monad.
runTestNested :: TestNested -> TestTree
runTestNested = runTestNestedIn []

-- | Descend into a name prefix.
testNested :: FilePath -> [TestNested] -> TestNested
testNested folderName =
    local (++ [folderName]) . fmap (testGroup folderName) . sequence

-- | Like `testNested` but adds a subdirectory corresponding to the GHC version being used.
testNestedGhc :: FilePath -> [TestNested] -> TestNested
testNestedGhc folderName = testNested (folderName </> ghcVersion)

-- Create a TestTree which runs in the directory 'path/<ghc-version>
runTestGroupNestedGhc :: [FilePath] -> [TestNested] -> TestTree
runTestGroupNestedGhc path = runTestNested . testNestedGhc (joinPath path)

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
nestedGoldenVsText :: TestName -> FilePath -> Text -> TestNested
nestedGoldenVsText name ext = nestedGoldenVsTextM name ext . pure

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsTextM :: TestName -> FilePath -> IO Text -> TestNested
nestedGoldenVsTextM name ext text = do
    path <- ask
    -- TODO: make more generic
    return $ goldenVsTextM name (foldr (</>) (name ++ ext ++ ".golden") path) text

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsDoc :: TestName -> FilePath -> Doc ann -> TestNested
nestedGoldenVsDoc name ext = nestedGoldenVsDocM name ext . pure

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsDocM :: TestName -> FilePath -> IO (Doc ann) -> TestNested
nestedGoldenVsDocM name ext val = nestedGoldenVsTextM name ext $ render <$> val
