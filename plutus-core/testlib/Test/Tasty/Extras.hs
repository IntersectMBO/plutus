{-# LANGUAGE BlockArguments        #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Test.Tasty.Extras
    ( Layer (..)
    , embed
    , nestWith
    , TestNestedM (..)
    , TestNested
    , runTestNestedM
    , testNestedNamedM
    , testNestedM
    , testNestedGhcM
    , runTestNested
    , testNestedNamed
    , testNested
    , testNestedGhc
    , goldenVsText
    , goldenVsTextM
    , goldenVsDoc
    , goldenVsDocM
    , nestedGoldenVsText
    , nestedGoldenVsTextPredM
    , nestedGoldenVsTextM
    , nestedGoldenVsDoc
    , nestedGoldenVsDocM
    , makeVersionedFilePath
    -- * Prettier equality assertions
    , assertEqualPretty
    , (%=?)
    , (%?=)
    , ignoreTestWhenHpcEnabled
    ) where

import PlutusPrelude hiding (toList)

import Control.Monad (unless)
import Control.Monad.Free.Church (F (runF), MonadFree, liftF)
import Control.Monad.Reader (MonadReader (ask, local), ReaderT (..), asks, mapReaderT)
import Data.ByteString.Lazy qualified as BSL
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import Data.Text.IO qualified as TIO
import Data.Text.Lazy qualified as Text
import Data.Version (showVersion)
import GHC.Exts (IsList (Item, fromList, toList))
import GHC.Stack (HasCallStack)
import System.FilePath (joinPath, (</>))
import System.Info (compilerVersion)
import Test.Tasty (TestName, TestTree, testGroup)
import Test.Tasty.ExpectedFailure (ignoreTest)
import Test.Tasty.Golden (createDirectoriesAndWriteFile, goldenVsStringDiff)
import Test.Tasty.Golden.Advanced (goldenTest)
import Test.Tasty.HUnit (Assertion, assertFailure)
import Text.Pretty.Simple (OutputOptions (..), defaultOutputOptionsDarkBg, pShowOpt)

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

{- | A monad allowing one to emit elements of type @a@. Semantically equivalent to
@Writer (DList a) r@, but:

1. is faster, being based on the Church-encoded free monad
2. implements 'Monoid', so that all the "Data.Foldable" convenience is supported
3. has better ergonomics as it doesn't require the user to wrap @a@ values into 'DList's

This type is also semantically equivalent to @Stream (Of a) Identity r@.

Useful for monadically creating tree-like structures, for example the following

> import Data.Tree
> yield = embed . pure
> main = putStrLn . drawTree . Node "a" . toList $ do
>     yield "b"
>     nestWith (Node "c") $ do
>         yield "d"
>         yield "e"
>     yield "f"

will produce

> -a
> |
> +- b
> |
> +- c
> |  |
> |  +- d
> |  |
> |  `- e
> |
> `- f
-}
newtype Layer a r = Layer
    { unLayer :: F ((,) a) r
    } deriving newtype (Functor, Applicative, Monad, MonadFree ((,) a))

instance unit ~ () => Semigroup (Layer a unit) where
    (<>) = (*>)

instance unit ~ () => Monoid (Layer a unit) where
    mempty = pure ()

instance unit ~ () => IsList (Layer a unit) where
    type Item (Layer a unit) = a
    fromList = traverse_ embed
    toList layer = runF (unLayer layer) mempty $ uncurry (:)

-- | Embed the given value into a 'Layer'-like type (either 'Layer' itself or a monad transformer
-- stack with 'Layer' at the bottom).
embed :: MonadFree ((,) a) m => a -> m ()
embed x = liftF (x, ())

-- | Collapse the given 'Layer' into a single element by converting it into a list, applying the
-- given function to the result and 'embed'ding it back.
nestWith :: ([a] -> a) -> Layer a () -> Layer a ()
nestWith f = embed . f . toList

newtype TestNestedM r = TestNestedM
    { unTestNestedM :: ReaderT [FilePath] (Layer TestTree) r
    } deriving newtype
        (Functor, Applicative, Monad, MonadReader [FilePath], MonadFree ((,) TestTree))

-- | A 'TestTree' of tests under some name prefix.
type TestNested = TestNestedM ()

instance unit ~ () => Semigroup (TestNestedM unit) where
    (<>) = (*>)

instance unit ~ () => Monoid (TestNestedM unit) where
    mempty = pure ()

-- | Run a 'TestNested' computation to produce a 'TestTree' (without actually executing the tests).
runTestNestedM :: [String] -> TestNested -> TestTree
runTestNestedM []   _    = error "Path cannot be empty"
runTestNestedM path test = testGroup (last path) . toList $ runReaderT (unTestNestedM test) path

-- | Descend into a folder.
testNestedNamedM
    :: FilePath  -- ^ The name of the folder.
    -> String    -- ^ The name of the test group to render in CLI.
    -> TestNested
    -> TestNested
testNestedNamedM folderName testName
    = TestNestedM
    . local (++ [folderName])
    . mapReaderT (nestWith $ testGroup testName)
    . unTestNestedM

-- | Descend into a folder for a 'TestNested' computation.
testNestedM :: FilePath -> TestNested -> TestNested
testNestedM folderName = testNestedNamedM folderName folderName

-- | Like 'testNestedM' but adds a subdirectory corresponding to the GHC version being used.
testNestedGhcM :: TestNested -> TestNested
testNestedGhcM = testNestedM ghcVersion

-- | Run a list of 'TestNested' computation to produce a 'TestTree' (without actually executing the
-- tests).
runTestNested :: [String] -> [TestNested] -> TestTree
runTestNested path = runTestNestedM path . fold

-- | Descend into a folder for a list of tests.
testNestedNamed
    :: FilePath  -- ^ The name of the folder.
    -> String    -- ^ The name of the test group to render in CLI.
    -> [TestNested]
    -> TestNested
testNestedNamed folderName testName = testNestedNamedM folderName testName . fold

-- | Descend into a folder for a list of 'TestNested' computations.
testNested :: FilePath -> [TestNested] -> TestNested
testNested folderName = testNestedM folderName . fold

-- | Like 'testNested' but adds a subdirectory corresponding to the GHC version being used.
testNestedGhc :: [TestNested] -> TestNested
testNestedGhc = testNestedGhcM . fold

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

{-| Compare the contents of a file under a name prefix against a 'Text'
using a predicate.
-}
nestedGoldenVsTextPredM
  :: TestName
  -- ^ The name of the test
  -> FilePath
  -- ^ The file extension
  -> IO Text
  -- ^ The text-producing action to execute
  -> (Text -> Text -> Bool)
  -- ^ How to compare golden file contents with the produced text
  -> TestNested
nestedGoldenVsTextPredM name ext action predicate = do
  filePath <- asks $ foldr (</>) (name ++ ".golden" ++ ext)
  embed $ goldenTest name (TIO.readFile filePath) action
    do \golden actual -> pure
        if predicate golden actual
          then Nothing
          else Just "Predicate failed on golden file"
    do createDirectoriesAndWriteFile filePath . BSL.fromStrict . encodeUtf8

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsTextM :: TestName -> FilePath -> IO Text -> TestNested
nestedGoldenVsTextM name ext text = do
    path <- ask
    embed $ goldenVsTextM name (foldr (</>) (name ++ ".golden" ++ ext) path) text

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsDoc :: TestName -> FilePath -> Doc ann -> TestNested
nestedGoldenVsDoc name ext = nestedGoldenVsDocM name ext . pure

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsDocM :: TestName -> FilePath -> IO (Doc ann) -> TestNested
nestedGoldenVsDocM name ext val = nestedGoldenVsTextM name ext $ render <$> val

{-| Asserts that the specified actual value is equal to the expected value.
The output message will contain the prefix, the expected value, and the
actual value.

If the prefix is the empty string (i.e., @\"\"@), then the prefix is omitted
and only the expected and actual values are output.
-}
assertEqualPretty
  :: (Eq a, Show a, HasCallStack)
  => String
  -- ^ The message prefix
  -> a
  -- ^ The expected value
  -> a
  -- ^ The actual value
  -> Assertion
assertEqualPretty preface expected actual =
  unless (actual == expected) (assertFailure msg)
 where
  msg =
    (if null preface then "" else preface)
      ++ "\n--- Expected: ---\n"
      ++ prettyStr expected
      ++ "\n\n--- Actual: ---\n"
      ++ prettyStr actual

  prettyStr :: Show a => a -> String
  prettyStr = Text.unpack . pShowOpt defaultOutputOptionsDarkBg
    { outputOptionsCompact = False
    , outputOptionsCompactParens = False
    , outputOptionsIndentAmount = 2
    , outputOptionsPageWidth = 120
    }

infix 1 %=?, %?=

{-| Asserts that the specified actual value is equal to the expected value
  (with the /expected/ value on the left-hand side).
-}
(%=?)
  :: (Eq a, Show a, HasCallStack)
  => a
  -- ^ The expected value
  -> a
  -- ^ The actual value
  -> Assertion
expected %=? actual = assertEqualPretty "" expected actual

{-| Asserts that the specified actual value is equal to the expected value
  (with the /actual/ value on the left-hand side).
-}
(%?=)
  :: (Eq a, Show a, HasCallStack)
  => a
  -- ^ The actual value
  -> a
  -- ^ The expected value
  -> Assertion
actual %?= expected = assertEqualPretty "" expected actual


{-|
Some tests inspect GHC code, but GHC code gets instrumented when using HPC
(Haskell Program Coverage), which causes those tests to fail.
This function disables those tests when the custom __HPC_ENABLED__ flag is defined.
-}
ignoreTestWhenHpcEnabled :: TestTree -> TestTree
ignoreTestWhenHpcEnabled t =
#ifdef __HPC_ENABLED__
    ignoreTest t
#else
    let _preventsUnusedBindsWarnings = ignoreTest t
    in t
#endif
