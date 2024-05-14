{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances  #-}

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
    , nestedGoldenVsTextM
    , nestedGoldenVsDoc
    , nestedGoldenVsDocM
    , makeVersionedFilePath
    ) where

import PlutusPrelude hiding (toList)

import Control.Monad.Free.Church (F (runF), MonadFree, liftF)
import Control.Monad.Reader
import Data.ByteString.Lazy qualified as BSL
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import Data.Version
import GHC.Exts
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

-- | Run a 'TestTree' of tests with a given name prefix. This doesn't actually run the tests:
-- instead it runs a computation in the Reader monad.
runTestNestedM :: [String] -> TestNested -> TestTree
runTestNestedM []   _    = error "Path cannot be empty"
runTestNestedM path test = testGroup (last path) . toList $ runReaderT (unTestNestedM test) path

-- | Descend into a folder.
testNestedNamedM
    :: FilePath    -- ^ The folder.
    -> String      -- ^ The name of the test to render in CLI.
    -> TestNested
    -> TestNested
testNestedNamedM folderName testName
    = TestNestedM
    . local (++ [folderName])
    . mapReaderT (nestWith $ testGroup testName)
    . unTestNestedM

-- | Descend into a folder.
testNestedM :: FilePath -> TestNested -> TestNested
testNestedM folderName = testNestedNamedM folderName folderName

-- | Like 'testNestedM' but adds a subdirectory corresponding to the GHC version being used.
testNestedGhcM :: TestNested -> TestNested
testNestedGhcM = testNestedM ghcVersion

runTestNested :: [String] -> [TestNested] -> TestTree
runTestNested path = runTestNestedM path . fold

testNestedNamed :: FilePath -> String -> [TestNested] -> TestNested
testNestedNamed folderName testName = testNestedNamedM folderName testName . fold

testNested :: FilePath -> [TestNested] -> TestNested
testNested folderName = testNestedM folderName . fold

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

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsTextM :: TestName -> FilePath -> IO Text -> TestNested
nestedGoldenVsTextM name ext text = do
    path <- ask
    embed $ goldenVsTextM name (foldr (</>) (name ++ ext ++ ".golden") path) text

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsDoc :: TestName -> FilePath -> Doc ann -> TestNested
nestedGoldenVsDoc name ext = nestedGoldenVsDocM name ext . pure

-- | Check the contents of a file under a name prefix against a 'Text'.
nestedGoldenVsDocM :: TestName -> FilePath -> IO (Doc ann) -> TestNested
nestedGoldenVsDocM name ext val = nestedGoldenVsTextM name ext $ render <$> val
